From ConCert Require Import Blockchain LocalBlockchain. 
From ConCert Require BAT Congress Congress_Buggy EIP20Token FA2Token.
From ConCert Require Import Serializable.
From QuickChick Require Import QuickChick.
From ConCert.Execution.QCTests Require Import CongressPrinters EIP20TokenPrinters FA2Printers TestContracts.

(* Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase. *)

Local Open Scope string_scope.

(* Currently we hack it to always deserialize to Msg types - only works for Congress! TODO: fix *)

(* Instance showSerializable {ty : Type} `{Show ty} : Show (Serializable ty) :=
{|
  show s := match (@deserialize ty _ s) with
            | Some ty => "SUCCESS"
            | None => "FAIL"
            end
|}. *)

Instance showSerializedValue : Show SerializedValue := 
{|
  show v := match @deserialize FA2Token.Msg _ v with
    | Some v => show v
    | None => 
    match @deserialize TestContracts.ClientMsg _ v with
    | Some v => show v
    | None =>
    match @deserialize TestContracts.TransferHookMsg _ v with
    | Some v => show v
    | None =>
    match @deserialize EIP20Token.Msg _ v with
    | Some v => show v
		| None =>
		match @deserialize Congress.Msg _ v with
		| Some v => show v
		| None => "<FAILED DESERIALIZATION>" 
		end
    end
    end
    end
    end
|}.


Close Scope string_scope.