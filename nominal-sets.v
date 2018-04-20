Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Import Lists.List.ListNotations.

Set Implicit Arguments.

Structure group :=
  {
    group_obj :> Type;
    group_id : group_obj;
    group_inv : group_obj -> group_obj;
    group_op : group_obj -> group_obj -> group_obj;
    group_assoc : forall x y z, group_op (group_op x y) z = group_op x (group_op y z);
    group_left_id : forall x, group_op group_id x = x;
    group_right_id : forall x, group_op x group_id = x;
    group_left_inv : forall x, group_op (group_inv x) x = group_id;
    group_right_inv : forall x, group_op x (group_inv x) = group_id;
  }.

Notation "1" := (group_id _).
Notation "x ^-1" := (group_inv _ x) (at level 30, format "x ^-1").
Notation "x * y" := (group_op _ x y).

Lemma test_group (G: group) (x: G) : x^-1 * x = 1.
Proof.
  apply group_left_inv.
Qed.

Lemma group_inv_unique (G: group) (g h: G) : g * h = 1 -> g^-1 = h.
Proof.
  intros H. rewrite <- (group_right_id _ (g^-1)). rewrite <- H, <- group_assoc.
  now rewrite group_left_inv, group_left_id.
Qed.

Lemma group_inv_id (G: group) : 1^-1 = (group_id G).
Proof.
  apply group_inv_unique. now apply group_left_id.
Qed.

Lemma group_inv_op (G: group) (g h: G) : (g * h)^-1 = h^-1 * g^-1.
Proof.
  apply group_inv_unique. rewrite group_assoc, <- (group_assoc _ h).
  rewrite group_right_inv, group_left_id. now apply group_right_inv.
Qed.

Structure homomorphism :=
  {
    group_source : group;
    group_target : group;
    hom : group_source -> group_target;
    hom_id: hom 1 = 1;
    hom_op: forall x y, hom (x * y) = (hom x) * (hom y);
    hom_inv: forall x, hom (x^-1) = (hom x)^-1;
  }.

(*
Structure G_set (G: group) :=
  {
    G_set_X :> Type;
    action: G -> G_set_X -> G_set_X;
    G_set_eq: relation G_set_X;
    G_set_equiv :> Equivalence G_set_eq;
    G_set_action_proper :> Proper (eq ==> G_set_eq ==> G_set_eq) action;
    G_set_id: forall x, G_set_eq (action 1 x) x;
    G_set_assoc: forall g h x, G_set_eq (action g (action h x)) (action (g * h) x);
  }.
Set Printing Coercions.
Set Printing Implicit.
Print G_set.
Check (fun G (X: G_set G) (x: X) => x).
*)

Class G_set (G: group) :=
  {
    G_set_X :> Type;
    action: G -> G_set_X -> G_set_X;
    G_set_eq: relation G_set_X;
    G_set_equiv :> Equivalence G_set_eq;
    G_set_action_proper :> Proper (eq ==> G_set_eq ==> G_set_eq) action;
    G_set_id: forall x, G_set_eq (action 1 x) x;
    G_set_assoc: forall g h x, G_set_eq (action g (action h x)) (action (g * h) x);
  }.

Notation "g ** x" := (action g x) (at level 45, right associativity).
Notation "x == y" := (G_set_eq x y) (at level 70, no associativity).
About action.
About G_set_eq.

Coercion G_set_to_type (G: group) : G_set G -> Type.
intros [X _ _ _ _ _ _]. exact X.
Defined.

Set Printing Coercions.
Set Printing Implicit.
Print G_set.
Check (fun G (X: G_set G) (x: X) => x).
Unset Printing Coercions.
Unset Printing Implicit.

Ltac gsimpl :=
  repeat progress rewrite ?group_left_id, ?group_right_id, ?group_left_inv, ?group_right_inv,
  ?group_inv_id, ?group_inv_op,
  ?G_set_id, ?G_set_assoc.

Print  G_set.
Lemma test_G_set (G: group) (X: G_set G) (x: G_set_X) (g: G): g ** g^-1 ** x == x.
Proof.
  now gsimpl.
Qed.

Definition equivariant_func (G: group) (X Y: G_set G) (F: X -> Y) (x: X) (g: G) :=
  F (g ** x) = g ** F x.
  
Definition prod_action (G: group) (X Y: G_set G) (g: G) (p: X * Y) : X * Y :=
  match p with
  | (x, y) => (g ** x, g ** y)
  end.

Arguments prod_action {G X Y}.

(*
Canonical Structure cartesian_prod (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X * Y)%type prod_action).
- intros [x y]. cbn. now gsimpl.
- intros g h [x y]. cbn. now gsimpl.
Defined.
*)

Definition prod_eq (G: group) (X Y: G_set G) (p1 p2: X * Y) :=
  match p1, p2 with
  | (x1, y1), (x2, y2) => x1 == x2 /\ y1 == y2
  end.

Instance cartesian_prod (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X * Y)%type prod_action (prod_eq X Y)).
- admit.
- intros g h H [x1 y1] [x2 y2] [H1 H2]. cbn. now rewrite H, H1, H2.
- intros [x y]. cbn. now gsimpl.
- intros g h [x y]. cbn. now gsimpl.
Admitted.

Definition union_action (G: group) (X Y: G_set G) (g: G) (s: X + Y) : X + Y :=
  match s with
  | inl x => inl (g ** x)
  | inr y => inr (g ** y)
  end.

Arguments union_action {G X Y}.

(*
Canonical Structure disjoint_union (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X + Y) union_action).
- intros [x|y]; cbn; now gsimpl.
- intros g h [x|y]; cbn; now gsimpl.
Defined.
*)

Definition union_eq (G: group) (X Y: G_set G) (s1 s2: X + Y) :=
  match s1, s2 with
  | inl x1, inl x2 => x1 == x2
  | inr y1, inr y2 => y1 == y2
  | _ , _ => False
  end.

Instance disjoint_union (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X + Y) union_action (union_eq X Y)).
- admit.
- intros g h -> [x1|y1] [x2|y2]; cbn; intros H; first [now rewrite H|destruct H].
- intros [x|y]; cbn; now gsimpl.
- intros g h [x|y]; cbn; now gsimpl.
Admitted.

Definition func_action (G: group) (X Y: G_set G) (g: G) (F: X -> Y) : X -> Y :=
  fun x => g ** F (g ^-1 ** x).

Arguments func_action {G X Y}.

(*
Canonical Structure func (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X -> Y) func_action).
- intros F. unfold func_action. rewrite G_set_id.
-
Abort.
*)

Definition func_eq (G: group) (X Y: G_set G) (F1 F2: X -> Y) := forall x1 x2, x1 == x2 -> F1 x1 == F2 x2.

Instance func (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X -> Y) func_action (func_eq X Y)).
- admit.
- intros g h -> F1 F2. unfold func_eq. intros H x1 x2 Hx. unfold func_action.
  rewrite (H _ (h^-1 ** x2)); [reflexivity|now rewrite Hx].
- intros F x1 x2 Hx. unfold func_action. gsimpl. admit.
- intros g h F x1 x2 Hx. unfold func_action. gsimpl. admit.
Admitted.

Definition equivariant_subset (G: group) (X: G_set G) (P: X -> Prop) :=
  forall g x, P x -> P (g ** x).

Inductive perm_minimal (A: Type) : list A -> list A -> Prop :=
  min_nil: perm_minimal [] []
| min_cons a a' l l': a <> a' -> perm_minimal l l' -> perm_minimal (a::l) (a'::l').

Lemma perm_minimal_comm (A: Type) (f g: list A) : perm_minimal f g -> perm_minimal g f.
Proof.
  revert g. induction f as [|a l IH]; intros g H.
  - inversion H. constructor.
  - inversion H. constructor; now auto.
Qed.

Structure perm (A: Type) :=
  {
    perm_f:> list A;
    perm_g: list A;
    perm_unique_f: NoDup perm_f;
    perm_unique_g: NoDup perm_g;
    perm_min: perm_minimal perm_f perm_g;
    (*
    perm_right_inv: forall a, f (g a) = a;
    perm_left_inv: forall a, g (f a) = a;
    *)
  }.

Definition transposition (A: Type) (pi: perm A) := length pi <= 1.

Definition perm_id (A: Type) : perm A.
apply (Build_perm (NoDup_nil A) (NoDup_nil A) (min_nil A)).
Defined.

Definition perm_inv (A: Type) (pi: perm A) : perm A.
destruct pi as [f g df_f df_g E]. apply (@Build_perm A g f df_g df_f). 
now apply perm_minimal_comm.
Defined.

Canonical Structure group_perm (A: Type) : group.
eapply (@Build_group _ (perm_id A) (@perm_inv A)).
