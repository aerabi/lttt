Require Import Base.
Require Import BaseProofs.

Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Decidable.

Module Type KeyModuleType.

  Parameter T : Type.
  Parameter equal : T -> T -> bool.
  Parameter eq_refl : forall x, equal x x = true.
  Parameter eq_extensionality : forall x y, equal x y = true -> x = y.

End KeyModuleType.

Module Type ValModuleType.

  Parameter T : Type.
  Parameter equal : T -> T -> bool.
  Parameter eq_refl : forall x, equal x x = true.

End ValModuleType.

Module moduleId <: KeyModuleType.

  Definition T := 𝔵.
  Definition equal : T -> T -> bool := var_eq.

  Lemma eq_refl : forall i, equal i i = true.
  Proof.
    intros. destruct i; simpl; apply nat_eq_refl.
  Qed.

  Lemma eq_extensionality : forall x y, equal x y = true -> x = y.
  Proof.
    intros. induction x; induction y; inversion H;
    apply nat_eq_to_eq in H1; subst n0; reflexivity.
  Qed.

End moduleId.

Module ListCtx  
  ( KM : KeyModuleType ) 
  ( VM : ValModuleType ).

  Definition K : Type := KM.T.
  Definition V : Type := VM.T.

  (* Inductive Definition of Key-Value List *)
  Inductive T : Type :=
  | empty : T
  | append : T -> K -> V -> T.

  Example unittest_T : forall k v, append empty k v <> empty.
  Proof.
    intros. unfold not. intros. inversion H.
  Qed.

  Proposition decide_append_empty : forall s k v, 
    empty = append s k v -> False.
  Proof.
    intros. inversion H.
  Qed.

  Definition null : T := empty.

  (* Equality *)
  Lemma equal_commut : forall (m1 m2 : T), m1 = m2 -> m2 = m1.
  Proof.
    intros. rewrite -> H. reflexivity.
  Qed.

  (* List Concat *)
  Fixpoint mult (s s' : T) : T :=
    match s, s' with
    | _, empty => s
    | empty, _ => s'
    | _, append t' k' v' => append (mult s t') k' v'
    end.

  Example unittest_mult : forall k k' v v',
    append (append empty k v) k' v' = mult (append empty k v) (append empty k' v').
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (* Notations *)
  Notation "s1 'o' s2" := (mult s1 s2) (at level 20, left associativity).

  (* Append and Concat *)
  Proposition id_r : forall m, m o null = m.
  Proof.
    intros. induction m; simpl; reflexivity.
  Qed.

  Proposition id_l : forall m, null o m = m.
  Proof.
    intros. induction m; simpl; reflexivity.
  Qed.

  Proposition inverse : forall s1 s2, s1 o s2 = null -> s1 = null /\ s2 = null.
  Proof.
    intros. induction s1; induction s2; auto.
    simpl in H. inversion H.
  Qed.

  Proposition append_to_concat : forall s' k v, 
    append s' k v = s' o (append empty k v).
  Proof.
    intros s. induction s.
    - intros. rewrite -> id_l. reflexivity.
    - intros k' v'. simpl. reflexivity.
  Qed.

  Proposition append_concat : forall s1 s2 s' k v, 
    s2 = append s' k v -> 
    s1 o s2 = append (s1 o s') k v.
  Proof.
    intros s1. induction s1.
    - intros. rewrite -> id_l. rewrite -> id_l. apply H.
    - intros s2 s' k' v' H. subst s2. simpl. reflexivity.
  Qed.

  (* Associativity of Concat *)
  Lemma assoc : forall m1 m2 m3, (m1 o m2) o m3 = m1 o (m2 o m3).
  Proof.
    intros m1; induction m1; intros m2; induction m2; intros m3; induction m3; simpl; try reflexivity.
    rewrite <- IHm3. simpl. reflexivity.
  Qed.

  (* Membership *)
  Inductive contains : T -> K -> V -> Prop :=
  | contains_append : forall s s' k v, s = append s' k v -> contains s k v
  | contains_append_set : forall s' k v k' v',
    contains s' k' v' -> k <> k' -> contains (append s' k v) k' v'.

  Example unittest_contains_overwrite : forall s k k' v v' v'',
    k <> k' ->
    s = append (append (append empty k v) k' v') k v'' ->
    contains s k v. (* We must not be able to prove this. *)
  Proof.
    intros. rewrite -> H0. try apply contains_append. apply contains_append_set.
  Abort.

  Example unittest_contains_overwrite' : forall s k k' v v' v'',
    k <> k' ->
    s = append (append (append empty k' v) k' v') k v'' ->
    contains s k' v. (* We must not be able to prove this. *)
  Proof.
    intros. rewrite -> H0. try apply contains_append. apply contains_append_set; try apply H.
    try apply contains_append. apply contains_append_set. 
  Abort.

  (* Contains Key *)
  Inductive contains_key : T -> K -> Prop :=
    contains_key_contains : forall (A : T) (k : K) (v : V),
      contains A k v -> contains_key A k.

  Proposition contains_key_extend : forall (A : T) (k k' : K) (v' : V),
    contains_key A k -> contains_key (append A k' v') k.
  Proof.
    intros. inversion H.
    assert (Hkk' : k = k' \/ k <> k'). { apply classic. } inversion Hkk'.
    - assert (Hkv' : contains (append A k' v') k v').
      { apply contains_append with (s' := A). rewrite <- H3. reflexivity. }
      apply contains_key_contains with (v := v'). apply Hkv'.
    - assert (Hkv : contains (append A k' v') k v).
      { apply contains_append_set; auto. }
      apply contains_key_contains with (v := v). apply Hkv.
  Qed.

  Corollary not_contains_key_shrink : forall (A : T) (k k' : K) (v' : V),
    ~ contains_key (append A k' v') k -> ~ contains_key A k.
  Proof.
    intros. unfold not in H. unfold not. intros Hfalse.
    apply contains_key_extend with (k' := k') (v' := v') in Hfalse. apply H in Hfalse.
    inversion Hfalse.
  Qed.

  (* Union *)
  Lemma union_l : forall (B C : T) (k : K) (v : V), 
    contains B k v -> ~ contains_key C k -> contains (B o C) k v.
  Proof.
    intros. induction C.
    - rewrite -> id_r. apply H.
    - assert (HX : B o append C k0 v0 = append (B o C) k0 v0).
      { apply append_concat. reflexivity. } rewrite -> HX.
      apply contains_append_set.
      + apply not_contains_key_shrink in H0. apply IHC in H0. auto.
      + unfold not. unfold not in H0. revert H0. rewrite -> contrapositive.
        * intros Hkk. rewrite -> Hkk. eapply contains_key_contains. eapply contains_append. reflexivity.
        * unfold decidable. apply classic.
  Qed.

  Lemma union_r : forall (B C : T) (k : K) (v : V),
    contains C k v -> contains (B o C) k v.
  Proof.
    intros. induction H.
    - rewrite -> H.
      assert (HX : B o append s' k v = append (B o s') k v).
      { apply append_concat. reflexivity. } rewrite -> HX.
      eapply contains_append. reflexivity.
    - assert (HX : B o append s' k v = append (B o s') k v).
      { apply append_concat. reflexivity. } rewrite -> HX.
      apply contains_append_set. apply IHcontains. auto.
  Qed.

  Lemma reunion : forall (B C : T) (k : K) (v : V),
    contains (B o C) k v -> contains B k v \/ contains C k v.
  Proof.
    intros. induction C.
    - left. rewrite -> id_r in H. apply H.
    - assert (HX : B o append C k0 v0 = append (B o C) k0 v0).
      { apply append_concat. reflexivity. } rewrite -> HX in H.
      inversion H.
      + subst k1 v1. inversion H0. subst k0 v0 s'.
        right. eapply contains_append. reflexivity.
      + subst s' k1 v1 k' v'. apply IHC in H5. inversion H5.
        * left. apply H0.
        * right. apply contains_append_set. apply H0. auto.
  Qed.

  (* Equivalence *)
  Definition subseteq (A B : T) : Prop := 
    forall (k : K) (v : V), contains A k v -> contains B k v.

  Definition eq (s s' : T) : Prop := subseteq s s' /\ subseteq s' s.

  Notation "s1 '≡' s2" := (eq s1 s2) (at level 82, left associativity).

  (* Equivalence Relation Axioms *)
  Proposition subseteq_reflexivity : forall m, subseteq m m.
  Proof.
    intros. unfold subseteq. intros k v. intros H. apply H.
  Qed.

  Proposition subseteq_transitivity : forall m1 m2 m3,
    subseteq m1 m2 -> subseteq m2 m3 -> subseteq m1 m3.
  Proof.
    intros m1 m2 m3 H H'. unfold subseteq in H. unfold subseteq in H'.
    unfold subseteq. intros k' v'. intros H''. apply H in H''.
    apply H' in H''. apply H''.
  Qed.

  Proposition eq_reflexivity : forall m, m ≡ m.
  Proof.
    intros. split; apply subseteq_reflexivity.
  Qed.

  Proposition eq_symmetry : forall m1 m2, m1 ≡ m2 -> m2 ≡ m1.
  Proof.
    intros. inversion H. split; try apply H0; try apply H1.
  Qed.

  Proposition eq_transitivity : forall m1 m2 m3,
    m1 ≡ m2 -> m2 ≡ m3 -> m1 ≡ m3.
  Proof.
    intros m1 m2 m3 H H'. inversion H. inversion H'.
    apply subseteq_transitivity with (m1 := m1) (m2 := m2) (m3 := m3) in H0.
    apply subseteq_transitivity with (m1 := m3) (m2 := m2) (m3 := m1) in H3.
    - split; try apply H0; try apply H3.
    - apply H1.
    - apply H2.
  Qed.

  (* Duplicate Keys *)
  Inductive duplicated : T -> Prop :=
  | duplicated_append : forall (A : T) (k : K) (v' : V),
      contains_key A k -> duplicated (append A k v')
  | duplicated_extend : forall (A : T) (k : K) (v' : V),
      duplicated A -> duplicated (append A k v').

  Definition unique_paired (A : T) : Prop := ~ duplicated A.

  Proposition unique_paired_shrink : forall (A : T) (k : K) (v : V),
    unique_paired (append A k v) -> unique_paired A.
  Proof.
    intros. unfold unique_paired. unfold not. unfold unique_paired in H. unfold not in H. revert H.
    apply contrapositive. { unfold decidable. apply classic. } apply duplicated_extend.
  Qed.

  Lemma unique_paired_either_or : forall (A B : T) (k : K),
    unique_paired (A o B) -> contains_key A k -> ~ contains_key B k.
  Proof.
    intros A B k Hu HcAk. unfold not. intros HcBk. induction B.
    - inversion HcBk. inversion H. inversion H2.
    - assert (Hu' : unique_paired (A o append B k0 v)). { auto. }
      rewrite -> append_concat with (s' := B) (k := k0) (v := v) in Hu; auto.
      apply unique_paired_shrink in Hu. apply IHB in Hu; auto. inversion HcBk. inversion H.
  Admitted.

  Lemma unique_paired_or_either : forall (A B : T) (k : K),
    unique_paired (A o B) -> contains_key B k -> ~ contains_key A k.
  Admitted.

  (* Well-Definedness and Contains Uniqueness *)
  Inductive ill_defined : T -> Prop :=
    duplicate_values : forall (A : T) (k : K) (v v' : V),
      contains A k v -> contains A k v' -> v <> v' -> ill_defined A.

  Definition well_defined (A : T) : Prop := ~ ill_defined A.

  Lemma contains_unique : forall (A : T) (k : K),
    well_defined A -> contains_key A k -> (exists! (v : V), contains A k v).
  Proof.
    intros A k H H'. inversion H'. subst A0 k0. exists v. unfold unique. split.
    - apply H0.
    - intros v'. unfold well_defined in H. unfold not in H. intros.
      (* reductio ad absurdum *)
      assert (Hx : v = v' \/ v <> v'). { apply classic. }
      inversion Hx; try apply H2. assert (Hf : ill_defined A). 
      { eapply duplicate_values. apply H0. apply H1. apply H2. }
      apply H in Hf. inversion Hf.
  Qed.

  Fixpoint to_function (A : T) (none : V) (k : K) : V :=
    match A with
    | append B k' v' => if KM.equal k k' then v' else to_function B none k
    | empty => none
    end.

  (* Commutativity *)
  Lemma eq_commut : forall (B C : T), unique_paired (B o C) -> B o C ≡ C o B.
  Proof.
    intros B C Hwd. unfold eq. split.
    - unfold subseteq. intros. apply reunion in H. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0. eapply unique_paired_or_either. apply Hwd.
        eapply contains_key_contains. apply H0.
    - unfold subseteq. intros. apply reunion in H. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0. eapply unique_paired_either_or. apply Hwd.
        eapply contains_key_contains. apply H0.
  Qed.

  (* Axioms of Extionsionality *)
  Axiom extensionality : forall (A B : T), eq A B -> A = B.

  Lemma extensionality_converse : forall (A B : T), A = B -> eq A B.
  Proof.
    intros. rewrite <- H. apply eq_reflexivity.
  Qed.

  Lemma extensionality_inverse : forall (A B : T), ~ eq A B -> A <> B.
  Proof.
    intros. unfold not. intros Hf. apply extensionality_converse in Hf.
    apply H in Hf. apply Hf.
  Qed.

  Lemma extensionality_contraposition : forall (A B : T), A <> B -> ~ eq A B.
  Proof.
    intros. unfold not. intros Hf. apply extensionality in Hf.
    unfold not in H. apply H in Hf. apply Hf.
  Qed.

  (* Commutativity *)
  Lemma commut : forall (B C : T), unique_paired (B o C) -> B o C = C o B.
  Proof.
    intros. apply extensionality. apply eq_commut. auto.
  Qed.

  (* Exchange *)
  Lemma exchange : forall A B C D, unique_paired (B o C) -> A o B o C o D = A o C o B o D.
  Proof.
    intros A B C D Hu.
    assert (H : B o C = C o B). { apply commut. auto. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> assoc. rewrite -> H'. reflexivity.
  Qed.

  Proposition append_commut : forall s k v k' v',
      unique_paired (append empty k v o append empty k' v') ->
      append (append s k v) k' v' = append (append s k' v') k v.
  Proof.
    intros. rewrite -> append_to_concat. rewrite -> append_to_concat.
    rewrite <- id_r with (m := s o (append empty k v) o (append empty k' v')).
    rewrite -> exchange; auto. rewrite -> id_r. repeat rewrite <- append_to_concat.
    reflexivity.
  Qed.

  Proposition append_commut_weak : forall s k v k' v', 
      k <> k' -> append (append s k v) k' v' = append (append s k' v') k v.
  Proof.
    intros. apply extensionality. unfold eq. split.
    - unfold subseteq. intros k'' v'' H''. inversion H''; try inversion H5.
      + inversion H0. apply contains_append_set. apply contains_append with (s' := s). reflexivity. intros [=].
        rewrite <- H8 in H6. rewrite -> H6 in H. unfold not in H. apply H. reflexivity.
      + inversion H7. eapply contains_append. reflexivity.
      + apply contains_append_set; auto. apply contains_append_set; auto.
    - unfold subseteq. intros k'' v'' H''. inversion H''; try inversion H5.
      + inversion H0. apply contains_append_set. apply contains_append with (s' := s). reflexivity. intros [=].
        rewrite <- H8 in H6. rewrite -> H6 in H. unfold not in H. apply H. reflexivity.
      + inversion H7. eapply contains_append. reflexivity.
      + apply contains_append_set; auto. apply contains_append_set; auto.
  Qed.

  (* Remove Key *)
  Fixpoint remove (A : T) (k : K) : T :=
    match A with
    | append B k' v' => 
      if KM.equal k k' then remove B k else append (remove B k) k' v'
    | empty => empty
    end.

  Lemma remove_not_contains : forall A k, ~ contains_key (remove A k) k.
  Proof.
    intros A. induction A. 
    - intros k. unfold not. intros Hf. simpl in Hf. inversion Hf. inversion H. inversion H2. 
    - intros k'. unfold not. intros Hf.
      assert (Ht : KM.equal k' k = true \/ KM.equal k' k <> true). { apply classic. } 
      inversion Ht.
      + simpl in Hf. rewrite -> H in Hf. apply IHA in Hf. apply Hf.
      + simpl in Hf. apply not_true_iff_false in H. rewrite -> H in Hf.
        inversion Hf. subst A0 k0. inversion H0.
        * subst k0 v1. inversion H1. subst k'.
          assert (H' : KM.equal k k = true). { apply KM.eq_refl. }
          rewrite -> H in H'. apply diff_false_true in H'. apply H'.
        * subst s' k0 v1 k'0 v0. apply contains_key_contains in H6.
          apply IHA in H6. apply H6.
  Qed.

  Proposition empty_contains_key : forall k, contains_key empty k -> False.
  Proof.
    intros. inversion H. inversion H0. inversion H3.
  Qed.

  Lemma remove_not_contained : forall (A : T) (k : K),
    ~ contains_key A k -> remove A k = A.
  Proof.
    intros A. induction A.
    - intros. simpl. reflexivity.
    - intros k' H. unfold not in H.
      assert (Ht : KM.equal k' k = true \/ KM.equal k' k <> true). { apply classic. } 
      inversion Ht.
      + assert (Hf : contains (append A k v) k v). { eapply contains_append. reflexivity. }
        apply KM.eq_extensionality in H0. subst k'. apply contains_key_contains in Hf.
        apply H in Hf. inversion Hf.
      + simpl in H. apply not_true_iff_false in H0. simpl. rewrite -> H0.
        assert (HX : ~ contains_key A k').
        { unfold not. intros Hf. inversion Hf. subst A0 k0.
          assert (HX' : contains (append A k v) k' v0). 
          { apply contains_append_set. apply H1. unfold not. intros Hfalse. rewrite <- Hfalse in H0.
            rewrite -> KM.eq_refl in H0. inversion H0. }
          apply contains_key_contains in HX'. apply H in HX'. apply HX'. }
        apply IHA in HX. rewrite -> HX. reflexivity.
  Qed.

  Corollary remove_empty : forall (k : K), remove empty k = empty.
  Proof.
    intros. apply remove_not_contained. unfold not. intros. inversion H.
    inversion H0. inversion H3.
  Qed.

  (* Remove Pair Once *)
  Fixpoint remove_pair (A : T) (k : K) (v : V) : T :=
    match A with
    | append B k' v' => 
      if andb (KM.equal k k') (VM.equal v v')
      then B
      else append (remove_pair B k v) k' v'
    | empty => empty
    end.

  Proposition remove_not_contained_pair : forall (A : T) (k : K) (v : V),
    ~ contains A k v -> remove_pair A k v = A.
  Proof.
    intros A. induction A. 
    - intros. simpl. auto.
    - intros. unfold not in H.
  Admitted.

  (* Set Minus *)
  Fixpoint set_minus (s s' : T) : T :=
    match s' with
    | empty => s
    | append t' k' v' => set_minus (remove_pair s k' v') t'
    end.

  Lemma set_minus_right_eliminate : forall A B k v,
    set_minus (append A k v) (append B k v) = set_minus A B.
  Proof.
    intros. simpl. rewrite -> KM.eq_refl. rewrite -> VM.eq_refl.
    simpl. auto.
  Qed.

  Proposition set_minus_append_non_member : forall G G' k v,
    ~ contains G k v ->
    set_minus G (append G' k v) = set_minus G G'.
  Proof.
    intros. simpl. rewrite -> remove_not_contained_pair; auto.
  Qed.

End ListCtx.