module DC.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

[@@ with_bytes bytes]
type message1 = {
  secret:bytes;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))

[@@ with_bytes bytes]
type message2 = {
  secret:bytes;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message =
  | Msg1 : message1 -> message
  | Msg2 : message2 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message
  = mk_parseable_serializeable ps_message
