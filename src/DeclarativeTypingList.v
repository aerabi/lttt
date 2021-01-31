Require Import Base.
Require Import BaseProofs.
Require Import ListCtx.

Require Import Coq.Bool.Bool.

Module module𝔗 <: ValModuleType.

  Definition T := 𝔗.
  Definition equal : T -> T -> bool := 𝔗_eq.

  Definition eq_refl : forall t, equal t t = true.
  Proof.
    intros. apply 𝔗_eq_refl.
  Qed.

End module𝔗.

Module module𝔄 <: ValModuleType.

  Definition T := 𝔄.
  Definition equal : T -> T -> bool := 𝔄_eq.

  Definition eq_refl : forall t, equal t t = true.
  Proof.
    intros. apply 𝔄_eq_refl.
  Qed.

End module𝔄.

(* Stores *)

Module m𝔊 := ListCtx.ListCtx moduleId module𝔗.
Module m𝔇 := ListCtx.ListCtx moduleId module𝔄.

Definition 𝔊 : Type := m𝔊.T.
Definition 𝔇 : Type := m𝔇.T.

(* Declarative Typing Rules for Type 𝔗 *)

Module DeclarativeTyping𝔗.

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

Module DeclarativeTyping𝔄.

Reserved Notation "Γ ';' Δ '⊢' t '|' T" (at level 60).

Inductive type : 𝔊 -> 𝔇 -> 𝔢 -> 𝔄 -> Prop :=
  | Var : forall Γ x A, Γ; (m𝔇.append m𝔇.empty x A) ⊢ 𝔢id x | A
  | 𝔄0_E : forall Γ Δ e B, Γ ; Δ ⊢ e | 𝔄0 -> Γ ; Δ ⊢ 𝔢holecase e | B
  | 𝔄1_I : forall Γ, Γ ; m𝔇.empty ⊢ 𝔢hole | 𝔄1
  | 𝔄1_E : forall Γ Δ1 Δ2 e1 e2 B, Γ ; Δ1 ⊢ e1 | 𝔄1 -> Γ ; Δ2 ⊢ e2 | B ->
      Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢holelet e1 e2 | B
  | 𝔄mult_I : forall Γ Δ1 Δ2 e1 e2 A1 A2, Γ ; Δ1 ⊢ e1 | A1 -> Γ ; Δ2 ⊢ e2 | A2 ->
      Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢pair e1 e2 | 𝔄mult A1 A2
  | 𝔄mult_E : forall Γ Δ1 Δ2 e1 e2 x1 x2 A1 A2 B,
      Γ ; Δ1 ⊢ e1 | 𝔄mult A1 A2 ->
      Γ ; (m𝔇.append (m𝔇.append Δ2 x1 A1) x2 A2) ⊢ e2 | B ->
      Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢let x1 x2 e1 e2 | B
  | 𝔄plus_I1 : forall Γ Δ e A1 A2, Γ ; Δ ⊢ e | A1 -> Γ ; Δ ⊢ 𝔢inj 1 e | 𝔄plus A1 A2
  | 𝔄plus_I2 : forall Γ Δ e A1 A2, Γ ; Δ ⊢ e | A2 -> Γ ; Δ ⊢ 𝔢inj 2 e | 𝔄plus A1 A2
  | 𝔄plus_E : forall Γ Δ1 Δ2 e e1 e2 x1 x2 A1 A2 B,
      Γ ; Δ1 ⊢ e | 𝔄plus A1 A2 ->
      Γ ; (m𝔇.append Δ2 x1 A1) ⊢ e1 | B ->
      Γ ; (m𝔇.append Δ2 x2 A2) ⊢ e2 | B ->
      Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢case e x1 e1 x2 e2 | B
  | 𝔄impl_I : forall Γ Δ e x A B, Γ ; (m𝔇.append Δ x A) ⊢ e | B -> Γ ; Δ ⊢ 𝔢lambda x e | 𝔄impl A B
  | 𝔄impl_E : forall Γ Δ1 Δ2 e1 e2 A B, Γ ; Δ1 ⊢ e1 | 𝔄impl A B -> Γ ; Δ2 ⊢ e2 | A ->
     Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢app e1 e2 | B
  | 𝔄diam_I : forall Γ Δ e A, Γ ; Δ ⊢ e | A -> Γ ; Δ ⊢ 𝔢return e | 𝔄diam A
  | 𝔄diam_E : forall Γ Δ1 Δ2 e1 e2 x A B,
     Γ ; Δ1 ⊢ e1 | 𝔄diam A ->
     Γ ; (m𝔇.append Δ2 x A) ⊢ e2 | 𝔄diam B ->
     Γ ; (m𝔇.mult Δ1 Δ2) ⊢ 𝔢bind x e1 e2 | 𝔄diam B
where "Γ ';' Δ '⊢' t '|' T" := (type Γ Δ t T).

End DeclarativeTyping𝔄.

Module DeclarativeTyping𝔗𝔄.

Module T𝔗 := DeclarativeTyping𝔗.
Module T𝔄 := DeclarativeTyping𝔄.

Definition type𝔗 := T𝔗.type.
Definition type𝔄 := T𝔄.type.

Notation "Γ '⊩' t '|' T" := (type𝔗 Γ t T) (at level 60).
Notation "Γ ';' Δ '⊢' t '|' T" := (type𝔄 Γ Δ t T) (at level 60).

Axiom 𝔗ceil_I : forall Γ e A, Γ ; m𝔇.empty ⊢ e | A -> Γ ⊩ 𝔱suspend e | ⌈A⌉.
Axiom 𝔗ceil_E : forall Γ t A, Γ ⊩ t | ⌈A⌉ -> Γ ; m𝔇.empty ⊢ 𝔢force t | A.
Axiom 𝔄flor_I : forall Γ t T, Γ ⊩ t | T -> Γ ; m𝔇.empty ⊢ 𝔢flor t | ⌊T⌋.
Axiom 𝔄flor_E : forall Γ Δ1 Δ2 e1 e2 x T B,
  Γ ; Δ1 ⊢ e1 | ⌊T⌋ ->
  m𝔊.append Γ x T ; Δ2 ⊢ e2 | B ->
  Γ ; m𝔇.mult Δ1 Δ2 ⊢ 𝔢florlet x e1 e2 | B.

End DeclarativeTyping𝔗𝔄.