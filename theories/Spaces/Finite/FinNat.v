Require Import
  HoTT.Basics
  HoTT.Basics.BooleanReflection
  HoTT.Types
  HoTT.HSet
  HoTT.Spaces.Nat
  HoTT.Spaces.Nat.Arithmetic
  HoTT.Spaces.Finite.Fin
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.DProp.

Local Open Scope nat_scope.

Definition FinNat (n : nat) : Type0 := {x : nat | x < n}.

Definition zero_finnat (n : nat) : FinNat n.+1
  := (0; leq_1_Sn).

Lemma path_zero_finnat (n : nat) (h : 0 < n.+1) : zero_finnat n = (0; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition succ_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1.+1; leq_S_n' u.1.+1 n u.2).
Check leq_S_n.

Lemma pred_finnat_subpf {n : nat} (j : nat) (p : j < n.+2) : pred j < n.+1.
  destruct j;  auto with nat.
Defined.

Definition pred_finnat {n : nat} (j : FinNat n.+2) : FinNat n.+1 :=
  (pred j.1; pred_finnat_subpf j.1 j.2).

Proposition sub_finnat_subpf {n : nat} (j : FinNat n) (k : nat) : j.1 - k < n.
Proof.
  destruct j; auto with nat.
Defined.

Definition sub_finnat {n : nat} (j : FinNat n) (k : nat) : FinNat n :=
  (j.1 - k; sub_finnat_subpf j k).
  
Lemma path_succ_finnat {n : nat} (u : FinNat n) (h : u.1.+1 < n.+1)
  : succ_finnat u = (u.1.+1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition last_finnat (n : nat) : FinNat n.+1
  := exist (fun x => x < n.+1) n (leq_refl n.+1).

Lemma path_last_finnat (n : nat) (h : n < n.+1)
  : last_finnat n = (n; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition incl_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1; leq_trans u.2 (leq_S n n (leq_n n))).

Lemma path_incl_finnat (n : nat) (u : FinNat n) (h : u.1 < n.+1)
  : incl_finnat u = (u.1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition finnat_ind (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : P n u.
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 u.1 u.2).
  - destruct u as [x h].
    destruct x as [| x].
    + exact (transport (P n.+1) (path_zero_finnat _ h) (z _)).
    + refine (transport (P n.+1) (path_succ_finnat (x; leq_S_n _ _ h) _) _).
      apply s. apply IHn.
Defined.

Lemma compute_finnat_ind_zero (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  (n : nat)
  : finnat_ind P z s (zero_finnat n) = z n.
Proof.
  cbn. by induction (hset_path2 1 (path_zero_finnat n leq_1_Sn)).
Defined.

Lemma compute_finnat_ind_succ (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n),
       P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : finnat_ind P z s (succ_finnat u) = s n u (finnat_ind P z s u).
Proof.
  refine
    (_ @ transport
          (fun p => transport _ p (s n u _) = s n u (finnat_ind P z s u))
          (hset_path2 1 (path_succ_finnat u (leq_S_n' _ _ u.2))) 1).
  destruct u as [u1 u2].
  assert (u2 = leq_S_n u1.+1 n (leq_S_n' u1.+1 n u2)) as p.
  - apply path_ishprop.
  - simpl. by induction p.
Defined.

Monomorphic Definition is_bounded_fin_to_nat {n} (k : Fin n)
  : fin_to_nat k < n.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + apply (@leq_trans _ n _).
      * apply IHn.
      * by apply leq_S.
    + apply leq_refl.
Defined.

Monomorphic Definition fin_to_finnat {n} (k : Fin n) : FinNat n
  := (fin_to_nat k; is_bounded_fin_to_nat k).

Monomorphic Fixpoint finnat_to_fin {n : nat} : FinNat n -> Fin n
  := match n with
     | 0 => fun u => Empty_rec (not_lt_n_0 _ u.2)
     | n.+1 => fun u =>
        match u with
        | (0; _) => fin_zero
        | (x.+1; h) => fsucc (finnat_to_fin (x; leq_S_n _ _ h))
        end
     end.

Lemma path_fin_to_finnat_fsucc {n : nat} (k : Fin n)
  : fin_to_finnat (fsucc k) = succ_finnat (fin_to_finnat k).
Proof.
  apply path_sigma_hprop.
  apply path_nat_fsucc.
Defined.

Lemma path_fin_to_finnat_fin_zero (n : nat)
  : fin_to_finnat (@fin_zero n) = zero_finnat n.
Proof.
  apply path_sigma_hprop.
  apply path_nat_fin_zero.
Defined.

Lemma path_fin_to_finnat_fin_incl {n : nat} (k : Fin n)
  : fin_to_finnat (fin_incl k) = incl_finnat (fin_to_finnat k).
Proof.
  reflexivity.
Defined.

Lemma path_fin_to_finnat_fin_last (n : nat)
  : fin_to_finnat (@fin_last n) = last_finnat n.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_succ {n : nat} (u : FinNat n)
  : finnat_to_fin (succ_finnat u) = fsucc (finnat_to_fin u).
Proof.
  cbn. do 2 f_ap. by apply path_sigma_hprop.
Defined.

Lemma path_finnat_to_fin_zero (n : nat)
  : finnat_to_fin (zero_finnat n) = fin_zero.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_incl {n : nat} (u : FinNat n)
  : finnat_to_fin (incl_finnat u) = fin_incl (finnat_to_fin u).
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 _ u.2).
  - destruct u as [x h].
    destruct x as [| x]; [reflexivity|].
    refine ((ap _ (ap _ (path_succ_finnat (x; leq_S_n _ _ h) h)))^ @ _).
    refine (_ @ ap fsucc (IHn (x; leq_S_n _ _ h))).
    by induction (path_finnat_to_fin_succ (incl_finnat (x; leq_S_n _ _ h))).
Defined.

Lemma path_finnat_to_fin_last (n : nat)
  : finnat_to_fin (last_finnat n) = fin_last.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - exact (ap fsucc IHn).
Defined.

Lemma path_finnat_to_fin_to_finnat {n : nat} (u : FinNat n)
  : fin_to_finnat (finnat_to_fin u) = u.
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 _ u.2).
  - destruct u as [x h].
    apply path_sigma_hprop.
    destruct x as [| x].
    + exact (ap pr1 (path_fin_to_finnat_fin_zero n)).
    + refine ((path_fin_to_finnat_fsucc _)..1 @ _).
      exact (ap S (IHn (x; leq_S_n _ _ h))..1).
Defined.

Lemma path_fin_to_finnat_to_fin {n : nat} (k : Fin n)
  : finnat_to_fin (fin_to_finnat k) = k.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + specialize (IHn k).
      refine (path_finnat_to_fin_incl (fin_to_finnat k) @ _).
      exact (ap fin_incl IHn).
    + apply path_finnat_to_fin_last.
Defined.

Definition equiv_fin_finnat (n : nat) : Fin n <~> FinNat n
  := equiv_adjointify fin_to_finnat finnat_to_fin
      path_finnat_to_fin_to_finnat
      path_fin_to_finnat_to_fin.


Local Definition nat_of_ord {n : nat} : FinNat n -> nat := pr1.

Coercion nat_of_ord : FinNat >-> nat.

Section WellFounded.
  (* 
     Our main goal in this section is to prove that if P is a decidable predicate on 
     finnat n, then either there is a *least i* in finnnat n such that P(i) holds, 
     or for all i, P i is false.
     Compare theories/bounded_search.v, except that we do not assume funext.
     For this theorem we require the order structure of [n] to speak of the "least i";  
     it is not clear how such a theorem would translate to a set merely equivalent to Fin n.
   *)

  (* Search from n+1 - k to n+1, decrementing k,
     for the least a in this range (inclusive of n+1-k) such that P(a) holds.
   *)
  Fixpoint finnat_wf_helper (n k : nat) {P : FinNat n.+1 -> Type}
    `{T : forall k, Decidable (P k)} : { a : FinNat n.+1 & P a } + Unit :=
    match k with
    | O => inr tt
    | S k' =>  match (T (n - k'; _ )) with
               | inl holds => inl ((n - k'; mixed_trans1 _ _ _ sub_less (n_lt_Sn _)); holds)
               | inr _ => finnat_wf_helper n k'
               end
    end.

  Lemma on_finnat_wf_helper (n : nat) {P : FinNat n.+1 -> Type}
      {T : forall k, Decidable (P k)} :
  forall k :nat, match (finnat_wf_helper n k) with
                 | inl a => (forall b : FinNat n.+1, P b -> (n.+1 - k <= b.1) -> a.1 <= b.1)
                 | inr _ => (forall b : FinNat n.+1, P b -> (n.+1 - k > b.1))
                             end.
  Proof.
    intro k; induction k; [ now intros [? ?] ? |].
    simpl finnat_wf_helper.
    destruct (T (n - k; _ )) as [tt | ff]; [ done |].
    destruct (finnat_wf_helper n k) as [val | none].
    + intros b pb ineq.
      assert (((n.+1 - k <= b) + (n - k = b))%type) as L. {
        specialize IHk with b. set (t := IHk pb).
        simpl in ineq. destruct (leq_split ineq);
          [left; exact (leq_trans (nataddsub_comm_ineq_lemma n k) l) | right; assumption].
      } 
      destruct L as [ll | rr]; intros;  [now apply IHk | contradiction ff ].
      set (j := (n - k; _)). assert (RW : j = b). { now (apply (injective proj1)). }
      symmetry in RW; now destruct RW.
    + intros b pf. simpl. specialize IHk with b; set (t := IHk pf).
      assert ( (n - k > b) + (n - k = b)) as L. {
        set (z:= i_lt_n_sum_m _ _ _ t);
          set (mk:= (@nataddpreserveslt _ _ k t)).
        rewrite ( (natminuspluseq _ _ z)) in mk.
        apply leq_S_n, (@natsubpreservesleq _ _  k) in mk.
         rewrite add_n_sub_n_eq in mk.
         destruct (leq_split mk); auto with nat.
      }
      destruct L; [ done | contradiction ff ].
      set (QQ :=(n-k;_)).
      assert (QQ = b) as RW by (now apply (injective proj1)); now rewrite RW.
  Qed.

  (* The following is a kind of combination LEM and well-foundedness theorem:
     For P a decidable predicate on [n], either there is a *minimal* k such that P(k),
     or there is no k in [n] such that P k.
     
   *)
  
Proposition finnat_wf {n : nat} (P : FinNat n -> Type) (T : forall k, Decidable (P k))
    : ~{ k : FinNat n & P k } +
        { x : FinNat n & (P x) /\ (forall x', P x' -> (x.1 <= x'.1))}.
Proof.
  destruct n;
    [ left; intros [a _]; destruct a; contradiction (not_lt_n_0 _ _); done |].
  assert (j := on_finnat_wf_helper n n.+1).
  destruct (finnat_wf_helper n n.+1) as [s | ?].
  - right. refine (s.1; (s.2,  _)).
    intro x'; specialize j with x';
      (* This line can be abstracted without losing anything. *)
      abstract(intro pf; apply j in pf; [ assumption | autorewrite with nat; auto with nat]).
  - left. abstract(intros [k p]; specialize j with k; apply j in p; autorewrite with nat in p;
    contradiction (not_lt_n_0 _ p)).
Defined.

(* Global Instance disj_dec {n : nat}  {P : FinNat n -> Type} {T : forall k, Decidable (P k)} : *)
(*   Decidable { k : FinNat n & P k}. *)
(* Proof. *)
(*   destruct (stdfinset_wf _ _). *)
(*   - now right. *)
(*   - left; exact (s.1; fst s.2). *)
(* Defined. *)

End WellFounded.
