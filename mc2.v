Require Import Setoid.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.

Axiom double_neg : forall P, P <-> ~~P.
Lemma fold_not : forall (P: Prop), (P -> False) <-> ~P. intuition auto. Defined.
Axiom forall_exists_duality1 : forall {T} (P: T -> Prop), ~ (exists x, P x) <-> (forall x, ~ P x).
Axiom forall_exists_duality2 : forall {T} (P: T -> Prop), ~ (forall x, P x) <-> (exists x, ~ P x).
Axiom DeMorgan1 : forall (P Q : Prop), ~(P /\ Q) <-> (~P \/ ~Q).
Axiom DeMorgan2 : forall (P Q : Prop), ~(P \/ Q) <-> (~P /\ ~Q).
Axiom TODO : False.

Ltac classical :=
  repeat match goal with
  | [ H : context[_ -> False] |- _ ] => rewrite (fold_not) in H (* sometimes intuition leaves us with negations like this. *)
  | [ H : context[~(~ _)]|- _ ] => rewrite <-double_neg in H
  | [ H : _ |- _ ] => rewrite DeMorgan1 in H
  | [ H : _ |- _ ] => rewrite DeMorgan2 in H
  | [ H: _ |- _] => erewrite forall_exists_duality1 in H
  | [ H: _ |- _] => erewrite forall_exists_duality2 in H
  | [ H : _ |- context[_ -> False] ] => rewrite (fold_not) (* sometimes intuition leaves us with negations like this. *)
  | [ H : _ |- context[~(~ _)] ] => rewrite <-double_neg
  | [ H : _ |- _ ] => rewrite DeMorgan1
  | [ H : _ |- _ ] => rewrite DeMorgan2
  | [ H: _ |- _] => erewrite forall_exists_duality1
  | [ H: _ |- _] => erewrite forall_exists_duality2
  end; try solve [intuition auto].  

Section LTLdef. 
  Context {T: Type}.
  Inductive LTL : Type :=
  injp_ltl : (T -> Prop) -> LTL
  | false_ltl : LTL
  | true_ltl : LTL
  | imp_ltl : LTL -> LTL -> LTL
  | until_ltl : LTL -> LTL -> LTL
  | next_ltl : LTL -> LTL.
  Definition TemInt : Type := nat -> T.
  Notation "φ U- ψ" := (until_ltl φ ψ) (at level 10).
  Definition from (k: nat): TemInt -> TemInt :=
      fun ζ n =>
        ζ (n+k).
  Notation "ζ ^^ k" := (from k ζ) (at level 10).

  Reserved Notation "ζ ⊨ φ" (at level 50, no associativity).
  Fixpoint models (ζ : TemInt) (φ : LTL) {struct φ}: Prop :=
      match φ with
      | injp_ltl p =>
        p (ζ 0)
      | imp_ltl ψ π =>
        (~(ζ ⊨ ψ) \/ (ζ ⊨ π))
      | next_ltl ψ =>
        (from 1 ζ) ⊨ ψ
      | until_ltl ψ π =>
        (exists (i:nat),
          ζ ^^ i ⊨ π
          /\ (forall j, j < i -> ζ ^^ j ⊨ ψ))
      | false_ltl =>
        False
      | true_ltl =>
        True
      end
  where "ζ ⊨ φ" := (models ζ φ).

  (* Fixpoint models_upto (k:nat) (ζ : TemInt) (φ : LTL): Prop := *)
  (*     match k with *)
  (*     | 0 => (* base case: modeling something for 0 cycles is vaccuously  *)
  (*               false. this is the only way to make until and next work out. *) *)
  (*            False *)
  (*     | (S k') => match φ with *)
  (*             | injp_ltl p => *)
  (*               p (ζ 0) (* to model an immediate property for the next S k' cycles, *)
  (*                          it suffices to satisfy it right now. *) *)
  (*             | imp_ltl ψ π => *)
  (*               (models_upto k ζ ψ) -> (models_upto k ζ π) *)
  (*             | next_ltl ψ => *)
  (*               (* next ψ says that ψ will be true in the next cycle. *)
  (*                  for this to be true for up to k cycles, *)
  (*                  we need that ψ is maintained for up to k-1 cycles by the suffix of ζ *) *)
  (*               models_upto k' (ζ ^^ 1) ψ *)
  (*             | until_ltl ψ π => *)
  (*               exists (i:nat), *)
  (*                 (i <= k) *)
  (*                 /\ models_upto (k-i) (ζ ^^ i) π (* note that this *doesn't* mean *)
  (*                                                    that π need be true for k-i cycles. *) *)
  (*                 /\ (forall j, j < i -> ζ ^^ j ⊨ ψ) *)
  (*             | false_ltl => *)
  (*               False *)
  (*             | true_ltl => *)
  (*               True *)
  (*       end *)
  (*     end. *)

  Fixpoint clarke_bm_helper (i k:nat) (ζ : TemInt) (φ : LTL): Prop :=
      match φ with
      | injp_ltl p =>
        p (ζ i)
      | imp_ltl ψ π =>
        (clarke_bm_helper i k ζ ψ) -> (clarke_bm_helper i k ζ π)
      | next_ltl ψ =>
        i < k /\ clarke_bm_helper (S i) k ζ ψ
      | until_ltl ψ π =>
        exists j, i <= j
             /\ j <= k
             /\ clarke_bm_helper j k ζ π
             /\ (forall b, (i <= b /\ b < j) ->
                     clarke_bm_helper b k ζ ψ)
      | false_ltl => False
      | true_ltl => True
      end.

  Definition clarke_bm k ζ φ: Prop := clarke_bm_helper 0 k ζ φ.


  Definition not_ltl (φ : LTL) : LTL := imp_ltl φ false_ltl.
  Definition ev_ltl (φ : LTL): LTL := true_ltl U- φ.
  Definition always_ltl (φ : LTL): LTL := not_ltl (ev_ltl (not_ltl φ)).
  Definition and_ltl (ϕ ψ : LTL) : LTL := not_ltl (imp_ltl ϕ (not_ltl ψ)).

  Theorem and_good : forall ζ ϕ ψ, ζ ⊨ ϕ /\ ζ ⊨ ψ <-> ζ ⊨ (and_ltl ϕ ψ).
  Proof.
    intros.
    split.
    { (* fwd *)
      intro.
      unfold  and_ltl,not_ltl.
      cbn.
      left.
      intro.
      repeat destruct H0; destruct H; auto.
    }
    {
      intro.
      split.
      {
        inversion H;
        cbn in H0;
        intuition auto;
        classical.
      }
      {
        inversion H; cbn in *; intuition auto; classical.
      }
    }
  Defined.

  Lemma ltl_not_good : forall ζ φ, ~ ζ ⊨ φ <-> ζ ⊨ (not_ltl φ).  
    Proof.
      (* Very lightly modified from a proof generated by GPT-3/copilot. *)  
      intros.
      split.
      { 
        intro H.
        unfold not_ltl.
        lazy.
        left.
        intro.
        repeat destruct H0; destruct H; auto.
      }
      {
        intro.
        inversion H; cbn in *; intuition auto; classical.
      }
    Defined.

  Theorem always_iff_loop_inv : forall (φ : LTL) (ζ : TemInt), 
    ζ ⊨ (always_ltl φ) 
    <-> (exists (i : nat), 
          (forall k, k >= i -> ζ ^^ k ⊨ φ -> ζ ^^ (k+1) ⊨ φ) /\ (forall (j : nat), j <= i -> ζ ^^ j ⊨ φ)).
  Proof.
    intros.
    split.
    { 
      intros H.
      exists 0.
      split; intros.
      {
        simpl in H.
        classical.
        destruct H; try solve [intuition auto].
        specialize (H (k+1)).
        classical.
        repeat destruct H; solve [intuition auto].
      } 
      {
        inversion H0.
        simpl in H.
        classical.
        destruct H; try solve [intuition auto].
        specialize (H 0).
        classical.
        repeat destruct H; try solve [intuition auto].
      }
    } 
    {
     intros H.  
     left.
     simpl.
     destruct H as [i [Hpres Hinit]].
     simpl.
     repeat (progress classical || intro).
     left.
     split; [|solve[intuition auto]].
     pose proof (lt_eq_lt_dec x i) as Hcompxi.
     repeat match goal with
            | [ H : context[{_} + {_}] |- _] => destruct H as [H | H]
            end; try solve [eapply Hinit;lia].
     {
      assert (Hstronger : forall n, ζ ^^ (i+n) ⊨ φ).
      {
        induction n.
        { 
          unshelve erewrite (_ : i + 0 = i). lia.
          eapply Hinit.
          auto.
        }
        { 
          unshelve erewrite (_ : i + S n = (i + n) + 1). lia.
          eapply Hpres.
          lia.
          auto.
        }
      }
      remember (x - i) as diff.
      unshelve erewrite (_ : x = i + diff); solve[lia || auto].
     }
    }
Defined.
End LTLdef.

Record Mealy : Type := mkMealy {
                           Σ : Type
                         ; Q : Type
                         ; δ : Q -> Σ -> Q * Σ
                         ; Q0 : Q
                         }.

Fixpoint MealyTrace' (M : Mealy) (I : nat -> Σ M) (n : nat) {struct n}: (Q M) * option (Σ M) :=
    match n with
    | 0 => ((Q0 M) , None)
    | S n' => let (Q', _) := MealyTrace' M I n' in
             match (δ M) Q' (I n') with
             | (q,σ) => (q, Some σ)
             end
    end.

Definition MealyTrace (M : Mealy) (I : nat -> Σ M) : @TemInt (Q M * option (Σ M)) :=
    fun n => MealyTrace' M I n.

Definition models_upto M k φ :=
      (* M models φ upto k cycles if (clake_bm k ζ φ) holds for all input traces I *)
      forall I, clarke_bm k (MealyTrace M I) φ.

Lemma MealyTrace0isQ0: forall M I, fst (MealyTrace M I 0) = Q0 M.
  auto.
Defined.

Search pair.

Definition state_seq (M: Mealy) : Type :=
    { s : nat -> Q M
      & { n : nat
          & ((forall t, (0 < t /\ t < n) ->
                  { input : Σ M & s t = fst ((δ M) (s (t - 1)) input) } ) * (s 0 = Q0 M))%type } }.

Definition len {M} (s : state_seq M) : nat := ltac:(repeat destruct s;
                                                  match goal with
                                                  | [ n : nat |- _ ] => exact n
                                                  end).

Definition state_fn {M} (s : state_seq M) : nat -> Q M := ltac:(repeat destruct s;
                                                       match goal with | [f : nat -> Q M |- _] => exact f
                                                       end).


Definition reachability_diameter (M : Mealy) : Type :=
  (* A reachability diameter D is a natural number such that every state reachable
     in n steps can also be reached in D <= n steps. *)
  { D : nat &
  forall (s : state_seq M) (n: nat) (_ : len s = n) (end_Q : Q M) (_ : (state_fn s) n = end_Q),
    (D <= n /\ exists (s' : state_seq M ), len s' = D /\ (state_fn s') D = end_Q) }.

Lemma repeats_past_rd : forall M I b D (_D: reachability_diameter M),
    D = projT1 _D ->
    b > D ->
    (exists k, (k >= 0 /\ k <= D) -> MealyTrace M I k = MealyTrace M I b).
  Proof.
    intros M I b D _D HD b_gt_D.
    destruct _D.
    simpl in *.
    symmetry in HD.
    subst.
    unshelve epose proof (_ : { s : state_seq M & (forall q : (Q M), exists (t : nat), t <= len s /\ (state_fn s) t = q)} ).
    {
      admit.
    }
    destruct X as [s pf].
    Abort. (* I don't think this is actually true, because it can take less time to reach a reachable state than to repeat a state *)

Theorem rd_sufficies_bmc_gp_case:
  forall (D: nat) (M: Mealy) (I: nat -> Σ M) (p: (Q M * option (Σ M)) -> Prop) (_D : reachability_diameter M),
    D = projT1 _D ->
    models_upto M D (always_ltl (injp_ltl p)) ->
    models (MealyTrace M I) (always_ltl (injp_ltl p)).
Proof.
  intros D M I p _D HD HBoundedModel.
  cbn in *.
  classical.
  left.
  intro.
  classical.
  left.
  split; intuition auto.
  unshelve epose proof (_ : forall I (x : nat),
                             (0 <= x /\
                              x <= D ->
                              (p (MealyTrace M I x)))).
  {
    intros I0 x0 ?.
    unfold models_upto, clarke_bm,clarke_bm_helper in HBoundedModel.
    simpl in HBoundedModel.
    setoid_rewrite forall_exists_duality1 in HBoundedModel.
    repeat setoid_rewrite DeMorgan1 in HBoundedModel.
    specialize (HBoundedModel I0 x0).
    classical.
    repeat match goal with
           | [H : _ \/ _ |- _] => destruct H
           | [H: exists _, _ |- _] => destruct H
           | [H: _ -> False |- _] => eapply H
           end; try solve[lia || auto].

  }
  change (p (MealyTrace M I x)).
  clear HBoundedModel.
  rename H into HBoundedModel.
  unfold reachability_diameter in _D.
  destruct _D as [D' Drd].
  simpl in HD.
  symmetry in HD.
  subst.
  destruct (PeanoNat.Nat.le_decidable x D).
  {
    (* x <= D *)
    specialize (HBoundedModel I x ltac:(lia)); auto.
  }
  {
    unshelve epose proof (_ : x > D) as Hgt.
    solve[lia].
    clear H.

    epose (q := fst (MealyTrace M I x)).
    (* constructing the always q state sequence *)
    unshelve epose proof ( _ : { s : state_seq M & (state_fn s (len s) = q /\ len(s) = x)}) as X.
    {
      unshelve econstructor.
      { unshelve econstructor.
        { exact (fun t => fst (MealyTrace M I t)). }
        { unshelve econstructor; try solve[exact x].
          split; [|auto].
          unshelve econstructor.
          exact (I (t-1)).
          Set Nested Proofs Allowed.
          Lemma mealy_unfold_step : forall M I t,
              t > 0 ->
              fst (MealyTrace M I t) = fst (δ M (fst (MealyTrace M I (t - 1))) (I (t - 1))).
            intros.
            destruct t.
            { lia. }
            {
              simpl.
              unshelve erewrite (_ : forall k, k - 0 = k). { lia. }
              unshelve destruct (MealyTrace M I t).
              simpl.
              Lemma fst_stupid: forall A B (p : A * B),
                  fst (let (a,b) := p in (a, Some b)) = fst p.
                intros.
                unfold fst.
                destruct p.
                auto.
              Defined.

              rewrite fst_stupid.
              reflexivity.
            }
          Defined.
          rewrite mealy_unfold_step.
          auto.
          lia.
        }
      }
      { simpl; auto. }
    }
    (* Now just need to use X... *)
    destruct X as [s [Hs H_len_s]].
    specialize (Drd s (len s) ltac:(auto) q Hs).
    destruct Drd as [HDlens seq_wit].
    destruct seq_wit as [s' [len_s'_is_D s'_ends_with_q]].
    unfold state_seq in s'.
    destruct s' as [s'fn [len_s' [s'connected s'start_ok]]]; simpl in *.
    unshelve epose proof (_ : nat -> Σ M) as I'.
    {
      (* defining I'(t) = if t <= D then i'_t else i'_D *)
      intro t.
      remember (PeanoNat.Nat.ltb t D) as pf.
      destruct pf.      
      {
        (* t < D case *)
        Search Nat.leb.
        assert (H_t_lt_D: t < D).
        { 
          eapply PeanoNat.Nat.ltb_lt;
          symmetry in Heqpf;
          assumption. 
        }
        
        remember (PeanoNat.Nat.eqb t 0) as pf2.
        destruct pf2.
        {
          (* t == 0 case*)  
          exact (I 0). (* this doesn't actually matter, so I just use a random alphabet symbol I had in context.*)
        }
        subst.
        assert (H_t_ne_0: t <> 0).
        {
          symmetry in Heqpf2.   
          eapply PeanoNat.Nat.eqb_neq.
          symmetry in Heqpf;
          assumption. 
        }
        assert (H_t_gt_0: t > 0). { solve[lia]. }
        unshelve epose proof (s'connected t _) as H_exists_input.
        lia.
        destruct H_exists_input as [input _].
        exact input.
      }
      {
        (* t >= D case, just use i'_D *)
        unshelve epose proof (s'connected (len_s' - 1) ltac:(case TODO)) as i'_D_and_pf.
        destruct i'_D_and_pf as [i'_D _].
        exact i'_D.
      }
    }
    {
      specialize (HBoundedModel I' x).
      assert (fst (MealyTrace M I' x) = fst (MealyTrace M I x)).
      {
        simpl.
        destruct (MealyTrace M I' x), (MealyTrace M I x), (δ M q0 (I' x)), (δ M q0 (I x)).
        simpl.
        rewrite IHx.
        r
        auto.

        induction x; simpl; [auto|].
        cbv in IHx.
        simpl.
        rewrite IHx.
        auto.
        simpl. }
    }

    ltac:(case TODO).
  }
  Defined.
