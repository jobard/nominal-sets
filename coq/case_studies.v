Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import PeanoNat.
Require Import List.
Import ListNotations.

Require Import nominal_set_def.

Set Implicit Arguments.


(** * Case Studies for Atoms, Lists and a Lambda Calculus *)

(*
Module fresh_atom.
  Definition max_list l := fold_left max l 0.
  Definition new_atom l := S (max_list l).

  Lemma fold_max_mono l n m : n <= m -> fold_left max l n <= fold_left max l m.
  Proof.
    revert n m. induction l; auto with arith.
    intros n m H. cbn. now apply IHl, Nat.max_le_compat_r.
  Qed.

  Lemma fold_max_inc l b : b <= fold_left max l b.
  Proof.
    induction l; auto.
    cbn. eapply le_trans. now apply IHl. apply fold_max_mono, Nat.le_max_l.
  Qed.

  Lemma all_le l : forall a, In a l -> a <= max_list l.
  Proof.
    induction l as [| b l IH]; intros a; [intros []|intros [E|H]].
    - rewrite E. cbn. apply fold_max_inc.
    - eapply le_trans. now apply IH. cbn. apply fold_max_mono. auto with arith.
  Qed.

  Lemma new_atom_fresh l a : new_atom l <= a -> ~ In a l.
  Proof.
    intros H H'. eapply Nat.nle_succ_diag_l.
    eapply Nat.le_trans; [exact H | now apply all_le].
  Qed.

  Lemma fresh_atom l: {a: atom | ~ In a l}.
  Proof.
    exists (new_atom l). intros H. now eapply new_atom_fresh, H.
  Qed.

End fresh_atom.

(* We can show now that if x has fintite support than we can compute a fresh atom for x. *)
Lemma fin_support_fresh_atom (X: perm_set) A (x: X) : support A x -> {a | a # x}.
Proof.
  intros H. destruct (fresh_atom.fresh_atom A) as [a H'].
  exists a. intros Su. unfold supp in Su. apply H', Su, H.
Qed.
*)


(** * Case Study: Atom as Perm-set *)

Section atom.
  (* We can define an action of permutations on atoms. *)
  Definition action_atom (pi: perm) a := pi a.

  (* Using the above action we can transform the set of atoms into a Perm-set. *)
  Canonical Structure G_set_atom : perm_set.
  apply (@Build_G_set group_perm atom action_atom).
  - intros a. now cbn.
  - intros g h x. now destruct g, h.
  Defined.

  (* This Perm-set over atoms is even nominal. *)
  Lemma nominal_atom : nominal G_set_atom.
  Proof. intros a. exists [a]. intros pi H. apply H. now constructor. Qed.

  Lemma supp_atom_refl a : supp a a.
  Proof.
    intros A Sa.
    pose (b := fresh_atom.new_atom (a::A)).
    assert (Hb: ~ In b A).
    - intros H. eapply (@fresh_atom.new_atom_fresh (a::A)); try reflexivity.
      now apply in_cons.
    - assert (nE: a <> b).
      + intros E. eapply (@fresh_atom.new_atom_fresh (a::A)); try reflexivity.
        rewrite E at 2. apply in_eq.
      + pose (pi := transp_perm a b).
        destruct (in_dec eq_nat_dec a A); auto.
        assert (H: pi ** a <> a) by (cbn; transpsimpl; auto).
        exfalso. apply H, Sa. intros x Hx. unfold pi.
        transptac; exfalso; subst; auto.
  Qed.

  Lemma supp_atom_unique a x : supp a x -> x = a.
    intros S. destruct (S [a]) as [H|[]]; auto.
    intros pi H. apply H. now constructor.
  Qed.

  Lemma atom_supp a x : supp a x <-> x = a.
  Proof.
    split.
    - apply supp_atom_unique.
    - intros E. rewrite E. apply supp_atom_refl.
  Qed.

  Lemma freshness_not_supp {Y: perm_set} a (y: Y) : freshness a y <-> a # y.
  Proof.
    split.
    - intros H S. apply (H a). split; auto. now apply supp_atom_refl.
    - intros nS x [Sa Sy]. apply nS. apply supp_atom_unique in Sa. now rewrite <- Sa.
  Qed.

End atom.

(** * Case Study: List as Perm-set *)

Section list.

  Definition action_list (X: perm_set) (pi: perm) (l: list X) :=
    map (fun x => (pi ** x)) l.

  Canonical Structure perm_set_list (X: perm_set) : perm_set.
  apply (Build_G_set group_perm (action_list X)).
  - intros l. induction l as [|x l IHl]; auto. cbn. gsimpl.
    unfold action_list in IHl. cbn in IHl. now rewrite IHl.
  - intros pi pi' l. induction l as [|x l IHl]. auto.
    cbn. gsimpl. unfold action_list in IHl. cbn in IHl. now rewrite IHl.
  Defined.

  Lemma list_support_refl A : support A A.
  Proof.
    induction A as [|a A IH]; intros pi H; auto.
    cbn. rewrite H; [|left; now auto].
    unfold support in IH. cbn in IH. unfold action_list in IH. rewrite IH; auto using in_cons.
  Qed.

  Lemma fresh_atom_list (l: list atom) : {a | a # l}.
  Proof. eapply fin_support_fresh_atom. eapply list_support_refl. Qed.

  Lemma list_supp (l : list atom) :
    forall a, supp l a <-> In a l.
  Proof.
    intros a. split.
    - apply supp_sub_support. apply list_support_refl.
    - induction l as [|x l IH]; cbn; intros H A S.
      + destruct H.
      + destruct H as [E| Ha].
        * rewrite E in S. apply supp_atom_refl.
          intros pi H. specialize (S pi H). now injection S.
        * apply IH; auto. intros pi H. specialize (S pi H). now injection S.
  Qed.

End list.


(** * Case Study: A Lambda Calculus as Perm-set *)

Section lambda_calculus.

  Inductive form :=
    var (a: atom) : form
  | app (s t: form) : form
  | lam (a: atom) (s: form) : form.

  Fixpoint action_form (pi: perm) (s: form) :=
    match s with
    | var a => var (pi a)
    | app s t => app (action_form pi s) (action_form pi t)
    | lam a s => lam (pi a) (action_form pi s)
    end.

  Canonical Structure perm_set_form : perm_set.
  apply (Build_G_set group_perm action_form).
  - intros s. induction s as [a|s IHs t IHt|a s IHs]; cbn in *; auto.
    + now rewrite IHs, IHt.
    + now rewrite IHs.
  - intros pi pi' s. revert pi pi'.
    induction s as [a|s IHs t IHt|a s IHs]; intros pi pi'; cbn in *.
    + now destruct pi, pi'; cbn.
    + now rewrite IHs, IHt.
    + rewrite IHs. now destruct pi, pi'; cbn.
  Defined.

  Fixpoint Var (s : form) :=
    match s with
    | var a => [a]
    | app s t => Var s ++ Var t
    | lam a s => a :: Var s
    end.

  Lemma var_fin_support (s: form) : support (Var s) s.
  Proof.
    induction s as [a|s IHs t IHt|a s IHs].
    - intros pi H. cbn. rewrite H; cbv; auto.
    - intros pi H. cbn. rewrite IHs, IHt; auto.
      + intros a ?. apply H. cbn. auto using in_or_app.
      + intros a ?. apply H. cbn. auto using in_or_app.
    - intros pi H. cbn. rewrite H, IHs; cbn; auto.
      intros x Vx. apply H. cbn. auto.
  Qed.

  Lemma fresh_atom_form (s: form) : {a | a # s}.
  Proof. eapply fin_support_fresh_atom. apply var_fin_support. Qed.

  Lemma var_supp (s : form) :
    forall a, supp s a <-> In a (Var s).
  Proof.
    intros a. split.
    - apply supp_sub_support. apply var_fin_support.
    - induction s as [x|s IHs t IHt|x s IHs]; cbn; intros H A S.
      + destruct H as [E| []]. rewrite E in S. apply supp_atom_refl.
        intros pi H. specialize (S pi H). now injection S.
      + apply in_app_or in H. destruct H as [Hs|Ht].
        * apply IHs; auto. intros pi H. specialize (S _ H). cbn in S. cbn. now injection S.
        * apply IHt; auto. intros pi H. specialize (S _ H). cbn in S. cbn. now injection S.
      + destruct H as [E|Hs].
        * rewrite E in S. apply supp_atom_refl.
          intros pi H. specialize (S pi H). now injection S.
        * apply IHs; auto. intros pi H. specialize (S _ H). cbn in S. cbn. now injection S.
  Qed.

  Lemma test1 a b :
    transp_perm a b ** (lam a (var a)) = lam b (var b).
  Proof.
    transptac.
  Qed.

  Lemma test2 a b :
    transp_perm a b ** (lam a (var a)) = transp_perm b a ** lam a (var a).
  Proof.
    transptac.
  Qed.

  Lemma test3 s a b :
    ~ In a (Var s) -> ~ In b (Var s) -> transp_perm a b ** (lam a s) = lam b s.
  Proof.
    intros H H'. transptac. apply f_equal. apply var_fin_support. intros.
    transptac.
    (* TODO automation *)
  Qed.

  Lemma var_equiv : equiv_func Var.
  Proof.
    intros s pi. induction s as [a|s IHs t IHt|a s IHs]; auto.
    - cbn. cbn in IHs, IHt. rewrite IHs, IHt. now rewrite map_app.
    - cbn. cbn in IHs. now rewrite IHs.
  Qed.

End lambda_calculus.

