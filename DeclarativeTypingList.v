Require Import Base.
Require Import BaseProofs.
Require Import ListCtx.

Require Import Coq.Bool.Bool.

Module Type Module𝔗 <: ValModuleType.

  Definition T := 𝔗.
  Definition equal : T -> T -> bool := 𝔗_eq.

  Definition eq_refl : forall t, equal t t = true.
  Proof.
    intros. apply 𝔗_eq_refl.
  Qed.

End Module𝔗.

Module Type Module𝔄 <: ValModuleType.

  Definition T := 𝔄.
  Definition equal : T -> T -> bool := 𝔄_eq.

  Definition eq_refl : forall t, equal t t = true.
  Proof.
    intros. apply 𝔄_eq_refl.
  Qed.

End Module𝔄.