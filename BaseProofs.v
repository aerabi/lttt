Require Import Base.

Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

(* Natural Numbers *)

Fixpoint nat_eq ( m : nat ) ( n : nat ) : bool :=
  match m, n with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S m', S n' => nat_eq m' n'
  end.

Proposition nat_eq_refl : forall n, nat_eq n n = true.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.

Lemma nat_eq_to_eq : forall m n, nat_eq m n = true -> m = n.
Proof.
  intros m. induction m; induction n; intros H.
  - reflexivity.
  - compute in H. inversion H.
  - compute in H. inversion H.
  - simpl in H. apply IHm in H. rewrite -> H. reflexivity.
Qed.

(* 𝔗 Type *)

Fixpoint 𝔗_eq ( T1 : 𝔗 ) ( T2 : 𝔗 ) : bool :=
  match T1, T2 with
  | Unit, Unit => true
  | Void, Void => true
  | 𝔗mult T1' T1'', 𝔗mult T2' T2'' => andb (𝔗_eq T1' T2') (𝔗_eq T1'' T2'')
  | 𝔗plus T1' T1'', 𝔗plus T2' T2'' => andb (𝔗_eq T1' T2') (𝔗_eq T1'' T2'')
  | 𝔗impl T1' T1'', 𝔗impl T2' T2'' => andb (𝔗_eq T1' T2') (𝔗_eq T1'' T2'')
  | 𝔗ceil T1', 𝔗ceil T2' => 𝔗_eq T1' T2'
  | _, _ => false
  end.

Definition 𝔗_eq_refl : forall t, 𝔗_eq t t = true.
Proof.
  intros. induction t; simpl; try rewrite -> andb_true_iff; try split; auto.
Qed.

(* Variables *)

Definition var_eq ( x : 𝔵 ) ( y : 𝔵 ) : bool :=
  match x, y with
  | 𝔵id m, 𝔵id n => nat_eq m n
  end.

Proposition var_eq_refl : forall x, var_eq x x = true.
Proof.
  intros. destruct x; simpl; apply nat_eq_refl.
Qed.

Lemma var_eq_to_eq : forall x y, var_eq x y = true -> x = y.
Proof.
  intros. destruct x. destruct y. inversion H. apply nat_eq_to_eq in H1.
  rewrite -> H1. reflexivity.
Qed.

