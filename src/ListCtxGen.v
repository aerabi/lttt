From QuickChick Require Import QuickChick.
Import GenLow GenHigh.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import List ZArith.
Import ListNotations.

Require Import Base.
Require Import BaseGen.
Require Import ListCtx.
Require Import ListCtxShow.
Require Import DeclarativeTypingList.

Import DeclarativeTypingList.
Import ListCtxShow.

Fixpoint gen_𝔊 (size : nat) : G m𝔊.T :=
  match size with 
  | O => elems [ m𝔊.empty ]
  | S size' => oneOf 
      [ liftGen3 m𝔊.append (gen_𝔊 size') (returnGen (𝔵id 0)) (gen_𝔗 size') ]
  end.

Sample (gen_𝔊 0).
Sample (gen_𝔊 1).
Sample (gen_𝔊  2).
Sample (gen_𝔊  3).
