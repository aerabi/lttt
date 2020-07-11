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
  | 𝔗mult_E2 : forall Γ t T1 T2, Γ ⊢ t | 𝔗mult T1 T2 -> Γ ⊢ 𝔱prj 2 t | T2
  | 𝔗plus_I1 : forall Γ t T1 T2, Γ ⊢ t | T1 -> Γ ⊢ 𝔱inj 1 t | 𝔗plus T1 T2
  | 𝔗plus_I2 : forall Γ t T1 T2, Γ ⊢ t | T2 -> Γ ⊢ 𝔱inj 2 t | 𝔗plus T1 T2
  | 𝔗plus_E : forall Γ t t1 t2 x1 x2 T1 T2 S, Γ ⊢ t | 𝔗plus T1 T2 -> 
      (m𝔊.append Γ x1 T1) ⊢ t1 | S -> (m𝔊.append Γ x2 T2) ⊢ t2 | S -> Γ ⊢ 𝔱case t x1 t1 x2 t2 | S
  | 𝔗impl_I : forall Γ t x T S, (m𝔊.append Γ x T) ⊢ t | S -> Γ ⊢ 𝔱lambda x t | 𝔗impl T S
  | 𝔗impl_E : forall Γ t1 t2 T S, Γ ⊢ t1 | 𝔗impl T S -> Γ ⊢ t2 | T -> Γ ⊢ 𝔱app t1 t2 | S
where "Γ '⊢' t '|' T" := (type Γ t T).

End DeclarativeTyping𝔗.