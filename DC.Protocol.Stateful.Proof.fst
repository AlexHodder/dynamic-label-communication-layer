module DC.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib

open DY.Lib.Label.DynamicLabel
open DY.Lib.Label.DynamicLabelEvent

open DC.Protocol.Total
open DC.Protocol.Total.Proof
open DC.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

(**** State Predicates ****)

let state_predicate_protocol: local_state_predicate dc_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | GeneratorState sender msg -> (
      let generator = prin in
      event_triggered tr generator (GeneratorSendMsg generator sender msg) /\
      is_knowable_by (join (principal_label generator) (principal_label sender)) tr msg.secret

    )
    | SenderState receiver msg -> (
      let sender = prin in
      event_triggered tr sender (SenderSendMsg sender receiver msg) /\
      Rand? msg.secret /\
      (
        get_label tr msg.secret == reveal_principal_label (Rand?.time msg.secret) \/
        is_publishable tr msg.secret
      )
      /\
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr msg.secret /\
      reveal_event_triggered tr sender receiver (Rand?.time msg.secret)
    )
    | ReceiverState msg -> (
      let receiver = prin in
      event_triggered tr receiver (ReceiverReceivedMsg receiver msg) /\
      is_knowable_by (principal_label receiver) tr msg.secret
    )
  );
  pred_later = (fun tr1 tr2 prin state_id st -> ());
  pred_knowable = (fun tr sender state_id st -> ())
}

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred state_predicate_protocol;
]

(**** Event Predicates ****)

let event_predicate_protocol: event_predicate dc_event =
  fun tr prin e ->
    match e with
    | GeneratorSendMsg generator sender msg -> (
      Rand? msg.secret /\
      is_secret (reveal_principal_label (Rand?.time msg.secret)) tr msg.secret /\
      reveal_event_triggered tr generator generator (Rand?.time msg.secret) /\
      reveal_event_triggered tr generator sender (Rand?.time msg.secret) /\
      is_knowable_by (join (principal_label generator) (principal_label sender)) tr msg.secret
    )
    | SenderSendMsg sender receiver msg -> (
      // exists generator. is_knowable_by (comm_label generator sender) tr msg.secret /\ event_triggered tr sender (CommConfReceiveMsg sender (serialize message (Msg2 msg)))
      True
    )
    | ReceiverReceivedMsg receiver msg -> (
      // (exists payload. event_triggered tr receiver (CommConfAuthReceiveMsg sender receiver payload)) /\
      // (
      //   event_triggered tr sender (SenderSendMsg sender receiver msg) \/
      //   is_corrupt tr (long_term_key_label sender)
      // )
      True
    )

val comm_layer_event_preds: comm_higher_layer_event_preds message
let comm_layer_event_preds = {
  default_comm_higher_layer_event_preds message with
  send_conf = (fun tr sender receiver payload ->     
    match payload with
    | Msg1 msg1 ->
      // for this message, the sender is the Generator and the receiver is the Sender --- should rename protocol participants probably...
      event_triggered tr sender (GeneratorSendMsg sender receiver msg1) /\
      Rand? msg1.secret /\
      is_secret (reveal_principal_label (Rand?.time msg1.secret)) tr msg1.secret /\
      is_knowable_by (comm_label sender receiver) tr msg1.secret
    | Msg2 msg2 -> event_triggered tr sender (SenderSendMsg sender receiver msg2)
);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
}

let reveal_event_pred : reveal_event_predicate =
  fun tr prin e -> True

let all_events = [
  event_predicate_communication_layer_and_tag comm_layer_event_preds;
  mk_event_tag_and_pred event_predicate_protocol;
  mk_event_tag_and_pred reveal_event_pred;
]

(**** Create the global trace invariants ****)

let trace_invariants_protocol: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global predicates contain all the local ones

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events

(**** Proofs ****)

val prepare_message1_proof :
  tr:trace -> generator:principal -> sender:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = prepare_message1 generator sender tr in
    trace_invariant tr_out
  ))
let prepare_message1_proof tr generator sender =
  reveal_opaque (`%mk_rand) (mk_rand);
  let (i, tr) = get_time tr in
  let (secret, tr) = mk_rand NoUsage (reveal_principal_label i) 32 tr in
 
  let (_, tr') = trigger_reveal_bytes_event generator generator secret tr in

  trigger_reveal_bytes_event_lemma tr generator generator secret;
  reveal_principal_label_can_flow_to_principal_label tr' generator generator i;
 
  let (_, tr'') = trigger_reveal_bytes_event generator sender secret tr' in

  trigger_reveal_bytes_event_lemma tr' generator sender secret;
  reveal_principal_label_can_flow_to_principal_label tr'' generator sender i

#push-options "--ifuel 3"
val send_message1_proof :
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> generator:principal -> state_id:state_id ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = send_message1 comm_keys_ids generator state_id tr in
    trace_invariant tr_out
  ))
let send_message1_proof tr comm_keys_ids generator state_id =
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options

// #push-options "--split_queries always"
val receive_message1_and_prepare_message2_proof :
  tr:trace -> comm_keys_ids : communication_keys_sess_ids -> sender:principal -> receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_message1_and_prepare_message2 comm_keys_ids sender receiver msg_id tr in
    trace_invariant tr_out
  ))
let receive_message1_and_prepare_message2_proof tr comm_keys_ids sender receiver msg_id =
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  
  match receive_confidential #message comm_keys_ids sender msg_id tr with
  | (Some msg, tr) -> (
    match guard_tr(Msg1? msg) tr with
    | (Some _, tr) -> (
      let Msg1 msg1 = msg in   
      let secret = msg1.secret in
      let msg2 : message2 = {secret} in
      match guard_tr(Rand? secret) tr with
      | (Some _, tr) -> (
        let i = Rand?.time msg2.secret in
        let (_, tr') = trigger_reveal_event sender receiver (Rand?.time secret) tr in
        trigger_reveal_event_trace_invariant reveal_event_pred sender receiver i tr;
        trigger_reveal_event_reveal_event_triggered sender receiver i tr;
        reveal_principal_label_can_flow_to_principal_label tr' sender receiver i;

        // not sure how to prove this - and also why we need it.
        
        // assume(exists generator.
        //   is_knowable_by (comm_label generator sender) tr msg2.secret /\ event_triggered tr sender (CommConfReceiveMsg sender (serialize message (Msg2 msg2)))
        // );

        let (_, tr'') = trigger_event sender (SenderSendMsg sender receiver msg2) tr' in

        // something to prove - should be possible, as secret is contained in the msg.
        assume(is_publishable tr' (serialize message msg) ==> is_publishable tr' secret);

        assert(is_knowable_by (comm_label sender receiver) tr'' secret \/ is_publishable tr'' (serialize message msg));
        
        assert(is_publishable tr'' secret ==> is_knowable_by (comm_label sender receiver) tr'' secret);

        assert(is_knowable_by (comm_label sender receiver) tr'' secret);

        let (state_id, tr''') = new_session_id sender tr'' in
        assert(trace_invariant tr''');
        let (_, tr4) = set_state sender state_id (SenderState receiver msg2) tr''' in
        
        assert(is_secret (reveal_principal_label i) tr' secret \/ is_publishable tr' (serialize message msg));

        assert(get_label tr' secret == reveal_principal_label i \/ is_publishable tr' (serialize message msg));
 
        assert(trace_invariant tr4);
        ()


      )
      | (None, tr) -> ()
    )
    | (None, tr) -> ()
  )
  | (None, _) -> ()
// #pop-options

#push-options "--ifuel 3"
val send_message2_proof :
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> sender:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = send_message2 comm_keys_ids sender sess_id tr in
    trace_invariant tr_out
  ))
let send_message2_proof tr comm_keys_ids sender sess_id =
    enable_core_comm_layer_lemmas comm_layer_event_preds;
    ()
#pop-options

#push-options "--ifuel 3"
val receive_message2_proof :
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_message2 comm_keys_ids receiver msg_id tr in
    trace_invariant tr_out
  ))
let receive_message2_proof tr comm_keys_ids receiver msg_id =
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options