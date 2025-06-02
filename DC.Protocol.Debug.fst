module DC.Protocol.Debug

open Comparse
open DY.Core
open DY.Lib

open DC.Protocol.Total
open DC.Protocol.Stateful

let debug () : traceful (option unit) =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  
  let generator = "generator" in
  let sender = "sender" in
  let receiver = "receiver" in

  let*? generator_comm_keys_sess_ids, sender_gen_comm_keys_sess_ids = initialize_communication generator sender in

  let*? sender_rec_comm_keys_sess_ids, receiver_comm_keys_sess_ids = initialize_communication sender receiver in

  let* generator_sess_id = prepare_message1 generator sender in

  let*? msg_id1 = send_message1 sender_gen_comm_keys_sess_ids sender generator_sess_id in

  let*? sender_session_id = receive_message1_and_prepare_message2 sender_gen_comm_keys_sess_ids sender receiver msg_id1 in

  let*? msg_id2 = send_message2 sender_rec_comm_keys_sess_ids sender sender_session_id in

  let*? receiver_session_id = receive_message2 receiver_comm_keys_sess_ids receiver msg_id2 in

  let* tr = get_trace in
  let _ = IO.debug_print_string (
    trace_to_string default_trace_to_string_printers tr
  ) in

  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options