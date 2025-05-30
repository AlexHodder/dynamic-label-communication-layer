module DC.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib

open DY.Lib.Label.DynamicLabel
open DY.Lib.Label.DynamicLabelEvent

open DC.Protocol.Total

(*** State type ***)

[@@with_bytes bytes]
type dc_state =
  | GeneratorState: sender:principal -> msg:message1 -> dc_state
  | SenderState: receiver:principal -> msg:message2 -> dc_state
  | ReceiverState : msg:message2 -> dc_state

%splice [ps_dc_state] (gen_parser (`dc_state))
%splice [ps_dc_state_is_well_formed] (gen_is_well_formed_lemma (`dc_state))

instance parseable_serializeable_bytes_dc_state: parseable_serializeable bytes dc_state
 = mk_parseable_serializeable ps_dc_state

instance local_state_dc_state: local_state dc_state = {
  tag = "DcConfAuthMessage.State";
  format = parseable_serializeable_bytes_dc_state;
}

(*** Event type ***)

[@@with_bytes bytes]
type dc_event =
  | GeneratorSendMsg: generator:principal -> sender:principal -> msg:message1 -> dc_event
  | SenderSendMsg: sender:principal -> receiver:principal -> msg:message2 -> dc_event
  | ReceiverReceivedMsg : receiver:principal -> msg:message2 -> dc_event

%splice [ps_dc_event] (gen_parser (`dc_event))
%splice [ps_dc_event_is_well_formed] (gen_is_well_formed_lemma (`dc_event))

instance event_dc_event: event dc_event = {
  tag = "DCConfAuthMessage.Event";
  format = mk_parseable_serializeable ps_dc_event;
}

val prepare_message1 : principal -> principal -> traceful state_id
let prepare_message1 generator sender =
  let* i = get_time in
  let* secret = mk_rand NoUsage (reveal_principal_label i) 32 in
  let msg1 : message1 = {secret} in

  // reveal the secret
  trigger_reveal_event generator generator i;*
  trigger_reveal_event generator sender i;*

  trigger_event generator (GeneratorSendMsg generator sender msg1);*
  let* state_id = new_session_id generator in
  set_state generator state_id (GeneratorState sender msg1);*
  return state_id

val send_message1 : communication_keys_sess_ids -> principal -> state_id -> traceful (option timestamp)
let send_message1 comm_keys_ids generator state_id =
  let*? st : dc_state = get_state generator state_id in
  guard_tr (GeneratorState? st);*?
  let GeneratorState sender msg = st in

  send_confidential comm_keys_ids generator sender (Msg1 msg)

val receive_message1_and_prepare_message2 : communication_keys_sess_ids -> principal -> principal -> timestamp -> traceful (option state_id)
let receive_message1_and_prepare_message2 comm_keys_ids sender receiver msg_id =
  let*? msg : message = receive_confidential #message comm_keys_ids sender msg_id in

  guard_tr(Msg1? msg);*?
  let Msg1 msg1 = msg in
  let msg2 : message2 = {secret=msg1.secret} in

  guard_tr(Rand? msg1.secret);*?
  trigger_reveal_event sender receiver (Rand?.time msg1.secret);*

  trigger_event sender (SenderSendMsg sender receiver msg2);*

  let* state_id = new_session_id sender in
  set_state sender state_id (SenderState receiver msg2);*
  return (Some state_id)

val send_message2 : communication_keys_sess_ids -> principal -> state_id -> traceful (option timestamp)
let send_message2 comm_keys_ids sender state_id =
  let*? st : dc_state = get_state sender state_id in
  guard_tr (SenderState? st);*?
  let SenderState receiver msg = st in

  send_confidential comm_keys_ids sender receiver (Msg2 msg)

val receive_message2 : communication_keys_sess_ids -> principal -> timestamp -> traceful (option state_id)
let receive_message2 comm_keys_ids receiver msg_id =
  let*? msg:message = receive_confidential comm_keys_ids receiver msg_id in

  guard_tr (Msg2? msg);*?
  let Msg2 msg2 = msg in

  trigger_event receiver (ReceiverReceivedMsg receiver msg2);*
  let* state_id = new_session_id receiver in
  set_state receiver state_id (ReceiverState msg2 <: dc_state);*
  return (Some state_id)