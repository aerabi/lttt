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

(* Declarative Typing Rules for Type 𝔗 *)

Module Type DeclarativeTyping𝔗
    ( m𝔵 : ModuleId )
    ( m𝔗 : Module𝔗 )
    ( m𝔊 : ListCtx.ListCtx m𝔵 m𝔗 ).

Definition 𝔊 : Type := m𝔊.T.

Reserved Notation "Γ '⊢' t '|' T" (at level 60).

Inductive type : 𝔊 -> 𝔱 -> 𝔗 -> Prop :=
  | Var : forall Γ x T, (m𝔊.append Γ x T) ⊢ (𝔱id x) | T
  | Unit_I : forall Γ, Γ ⊢ 𝔱hole | Unit
  | Void_E : forall Γ t T, Γ ⊢ t | Void -> Γ ⊢ 𝔱holecase t | T
  | 𝔗mult_I : forall Γ t1 t2 T1 T2, Γ ⊢ t1 | T1 -> Γ ⊢ t2 | T2 -> Γ ⊢ 𝔱pair t1 t2 | 𝔗mult T1 T2
  | 𝔗mult_E1 : forall Γ t T1 T2, Γ ⊢ t | 𝔗mult T1 T2 -> Γ ⊢ 𝔱prj 1 t | T1
where "Γ '⊢' t '|' T" := (type Γ t T).

End DeclarativeTyping𝔗.