From QuickChick Require Import QuickChick.
Import GenLow GenHigh.

Require Import List ZArith.
Import ListNotations.

Require Import String. Open Scope string.

Require Import Base.
Require Import BaseGen.
Require Import BaseShow.
Require Import BaseProofs.
Require Import ListCtx.
Require Import ListCtxGen.
Require Import ListCtxShow.
Require Import DeclarativeTypingList.
Require Import OperationalSemantics.

Import DeclarativeTypingList.
Import DeclarativeTyping𝔗𝔄.

Conjecture 𝔱_preservation : forall Γ t t' T, type𝔗 Γ t T -> 𝔱sem t t' -> type𝔗 Γ t' T.

Definition 𝔱_preservation_fun (Γ : m𝔊.T) (t t' : 𝔱) (T : 𝔗) := 
    (type𝔗 Γ t T -> 𝔱sem t t' -> type𝔗 Γ t' T).

Import BaseGen.
Import BaseShow.
Import BaseProofs.
Import ListCtxGen.

Definition 𝔗_fun (T : 𝔗) := 𝔗_eq T T.

QuickChick 𝔗_fun.