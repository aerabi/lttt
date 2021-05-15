From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.

Require Import Base.
Require Import BaseGen.
Require Import BaseShow.
Require Import BaseProofs.
Require Import ListCtx.
Require Import DeclarativeTypingList.

Import DeclarativeTypingList.
Import BaseShow.

Instance show_𝔊 : Show m𝔊.T := 
  {| show :=
      let fix aux G :=
      match G with
      | m𝔊.empty => "[]"
      | m𝔊.append G' k v => aux G' ++ " : (x, " ++ (show v) ++ ")"
      end
      in aux
  |}.
