module DC.Protocol.SecurityProperties

open Comparse
open DY.Core
open DY.Lib

open DC.Protocol.Total
open DC.Protocol.Total.Proof
open DC.Protocol.Stateful
open DC.Protocol.Stateful.Proof

open DY.Lib.Label.DynamicLabel
open DY.Lib.Label.DynamicLabelEvent

val secret_secrecy_generator:
  tr:trace -> generator:principal -> sender:principal -> msg:message1 ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr msg.secret /\
    (exists sess_id. state_was_set tr sender sess_id (GeneratorState sender msg)) /\
    Rand? msg.secret
  )
  (ensures
    exists revealer prin.
      reveal_event_triggered tr revealer prin (Rand?.time msg.secret) /\
      is_corrupt tr (principal_label prin)
  )
let secret_secrecy_generator tr generator sender msg =
  attacker_only_knows_publishable_values tr msg.secret;
  ()