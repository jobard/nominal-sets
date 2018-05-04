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


(** Case Studies for Atoms, Lists and a Lambda Calculus *)
(* TODO: intro *)


(** * Case Study: Atom as Perm-set *)
(* In out first case study we have a look at atoms as Perm-set. We show that this
   Perm-set is even nominal and characterize supp precisely. Also, both freshness
   notions coincide in this case. *)

Section atom.
  (* We can define an action of permutations on atoms by function application. *)
  Definition action_atom (pi: perm) a := pi a.

  (* Using the above action we can transform the type of atoms into a Perm-set. *)
  Canonical Structure perm_set_atom : perm_set.
  apply (@Build_G_set group_perm atom action_atom).
  - intros a. now cbn.
  - intros g h x. now destruct g, h.
  Defined.

  (* From the definitions it follows that [a] supports a. *)
  Lemma support_atom a : support [a] a.
  Proof. intros pi H. auto using in_eq. Qed.

  (* Thus, this Perm-set over atoms is even nominal. *)
  Lemma nominal_atom : nominal perm_set_atom.
  Proof. intros a. exists [a]. apply support_atom. Qed.

  (* There is always a fresh atom for an atom a. *)
  Lemma fresh_atom (a: atom) : {x | x # a}.
  Proof. apply (@support_fresh_atom _ [a]). apply support_atom. Qed.

  (* We show that supp is reflexive. Given a support A for a, we use a transposition
     pi of a and b, where b is an atom different from a not occuring in A. The proof
     is closed by a case distinction whether A contains a or not. The tactics for
     transpositions are helpful to deal with the pi in a nice way. *)
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

  (* It follows easliy that the atoms for which supp holds are unique. *)
  Lemma supp_atom_unique a x : supp a x -> x = a.
  Proof.
    intros S. destruct (S [a]) as [H|[]]; auto using support_atom.
  Qed.

  (* Both lemmas above characterize supp precisely. *)
  Lemma atom_supp a x : supp a x <-> x = a.
  Proof.
    split.
    - apply supp_atom_unique.
    - intros E. rewrite E. apply supp_atom_refl.
  Qed.

  (* By using the precise characterization of supp, we can show that both freshness
     notions coincide. *)
  Lemma freshness_not_supp {Y: perm_set} a (y: Y) : freshness a y <-> a # y.
  Proof.
    split.
    - intros H S. apply (H a). split; auto. now apply supp_atom_refl.
    - intros nS x [Sa Sy]. apply nS. apply supp_atom_unique in Sa. now rewrite <- Sa.
  Qed.

End atom.


(** * Case Study: List as Perm-set *)
(* Our second case study regards lists over a Perm-set as Perm-set. If we restrict 
   ourselves to lists over atoms then this Perm-set is nominal and supp of some list
   is precisely characterized by the list itself. *)

Section list.

  (* A permutation acts on a list by acting on all elements. *)
  Definition action_list (X: perm_set) (pi: perm) (l: list X) :=
    map (fun x => (pi ** x)) l.

  (* Above action results in a Perm-set. *)
  Canonical Structure perm_set_list (X: perm_set) : perm_set.
  apply (Build_G_set group_perm (action_list X)).
  - intros l. induction l as [|x l IHl]; auto. cbn. gsimpl.
    unfold action_list in IHl. cbn in IHl. now rewrite IHl.
  - intros pi pi' l. induction l as [|x l IHl]. auto.
    cbn. gsimpl. unfold action_list in IHl. cbn in IHl. now rewrite IHl.
  Defined.

  (* Support is reflexive for lists over atom. *)
  Lemma list_support_refl A : support A A.
  Proof.
    induction A as [|a A IH]; intros pi H; auto.
    cbn. rewrite H; [|left; now auto].
    unfold support in IH. cbn in IH. unfold action_list in IH.
    rewrite IH; auto using in_cons.
  Qed.

  (* Thus, the Perm-set of lists over atoms is nominal. *)
  Lemma nominal_list : nominal (perm_set_list (perm_set_atom)).
  Proof. intros A. exists A. apply list_support_refl. Qed.

  (* There is always a fresh atom for a list. *)
  Lemma fresh_atom_list (l: list atom) : {a | a # l}.
  Proof. eapply support_fresh_atom. eapply list_support_refl. Qed.

  (* Supp of a list is precisely characterized by the list itself. *)
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
(* Our last case study is about a lambda calculus. We show again that this is a
   nominal Perm-set and supp is precisely characterized by the occuring variables.
   The function computing the occuring variables is also equivariant. *)

Section lambda_calculus.

  (* Our formulas consists of variables, function applications and lambda terms which
     bind a atom. *)
  Inductive form :=
    var (a: atom) : form
  | app (s t: form) : form
  | lam (a: atom) (s: form) : form.

  (* The action of a permutation is performed on all variables including those bound
     by lambda terms. *)
  Fixpoint action_form (pi: perm) (s: form) :=
    match s with
    | var a => var (pi a)
    | app s t => app (action_form pi s) (action_form pi t)
    | lam a s => lam (pi a) (action_form pi s)
    end.

  (* Above action yields a Perm-set on formulas. *)
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

  (* We can compute the variables occuring in a formula. *)
  Fixpoint Var (s : form) :=
    match s with
    | var a => [a]
    | app s t => Var s ++ Var t
    | lam a s => a :: Var s
    end.

  (* The function Var is equivariant. *)
  Lemma var_equiv : equiv_func Var.
  Proof.
    intros s pi. induction s as [a|s IHs t IHt|a s IHs]; auto.
    - cbn. cbn in IHs, IHt. rewrite IHs, IHt. now rewrite map_app.
    - cbn. cbn in IHs. now rewrite IHs.
  Qed.

  (* The list of occuring variables supports a formula. *)
  Lemma var_support (s: form) : support (Var s) s.
  Proof.
    induction s as [a|s IHs t IHt|a s IHs].
    - intros pi H. cbn. rewrite H; cbv; auto.
    - intros pi H. cbn. rewrite IHs, IHt; auto.
      + intros a ?. apply H. cbn. auto using in_or_app.
      + intros a ?. apply H. cbn. auto using in_or_app.
    - intros pi H. cbn. rewrite H, IHs; cbn; auto.
      intros x Vx. apply H. cbn. auto.
  Qed.

  (* Thus, the Perm-set of formulas is nominal. *)
  Lemma nominal_form : nominal (perm_set_form).
  Proof. intros s. exists (Var s). apply var_support. Qed.

  (* There is always a fresh atom for a formula s. *)
  Lemma fresh_atom_form (s: form) : {a | a # s}.
  Proof. eapply support_fresh_atom. apply var_support. Qed.

  (* Supp is precisely characterized by the list of occuring variables.
     This follows by induction and the fact that supp is reflexive on atoms. *)
  Lemma var_supp (s : form) :
    forall a, supp s a <-> In a (Var s).
  Proof.
    intros a. split.
    - apply supp_sub_support. apply var_support.
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
    intros H H'. transptac. apply f_equal. apply var_support. intros.
    transptac.
  Qed.

End lambda_calculus.

