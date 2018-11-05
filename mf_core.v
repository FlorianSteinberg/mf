(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set.
Require Import CRelationClasses Morphisms.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module mf.
Structure type S T := Pack {
value:> S -> (mf_subset.type T);
}.
End mf.
Notation mf := mf.type.
Coercion mf.value: mf >-> Funclass.
Notation "S ->> T" := (mf S T) (at level 50).
Definition make_mf S T (f: S -> T -> Prop) := mf.Pack (fun s => mf_subset.Pack (fun t => f s t)).

(* The following should be considered to define equality as multivalued functions *)
Definition equiv S T (f g: S ->> T) := (forall s, f s === g s).

Definition mf_iff S T f g := forall (s: S) (t: T), f s t <-> g s t.
Global Instance make_mf_prpr S T: Proper (@mf_iff S T ==> @equiv S T) (@make_mf S T).
Proof. done. Qed.

Global Instance eqiuv_equiv S T: Equivalence (@equiv S T).
Proof.
split => // [f g eq s t | f g h feg geh s t]; first by split => [gst | fst]; apply eq.
by split => [fst | hst]; [apply geh; apply feg | apply feg; apply geh].
Qed.
Notation "f =~= g" := (equiv f g) (at level 70).

Global Instance value_prpr S T:
	Proper (@equiv S T ==> eq ==> (@set_equiv T)) (@mf.value S T).
Proof. by move => P Q eq s _ <-; apply eq. Qed.

Section Basics.
Definition F2MF S T (f : S -> T) : (S ->> T) := make_mf (fun s t => f s = t).
(* I'd like this to be a Coercion but it won't allow me to do so. *)
Global Instance F2MF_prpr S T: Proper (@eqfun T S ==> @equiv S T) (@F2MF S T).
Proof. by move => f g eq s t; rewrite /F2MF /= eq. Qed.

Definition inverse S T (f: S ->> T) := make_mf (fun t s => f s t).
Notation inv f := (inverse f).
Notation "f '\inverse'" := (inverse f) (at level 50).
Notation "f '\^-1'" := (inverse f) (format "f '\^-1'", at level 50).
Definition mf_inverse S T := F2MF (@inverse S T).

Lemma inv_inv S T (f: S ->> T): (f\^-1)\^-1 =~= f.
Proof. done. Qed.

Global Instance inv_prpr S T: Proper ((@equiv S T) ==> (@equiv T S)) (@inverse S T).
Proof. by move => f g eq s t; apply (eq t s). Qed.

Definition inv_img S T (f: S ->> T) (P: mf_subset.type T) := make_subset (fun s => exists t, f s t /\ P t).
Lemma invimg_spec S T (f: S ->> T) P s : inv_img f P s <-> intersects P (f s).
Proof. by split; move => [t []]; exists t. Qed.

Definition img S T (f: S ->> T) P := inv_img (inv f) P.

(* The domain of a multifunctions is the set of all inputs such that the value set
is not empty. *)
Definition dom S T (f: S ->> T) := make_subset (fun s => exists t, f s t).

Lemma dom_crct S T f (s: S): s \from dom (make_mf f) <-> exists (t: T), f s t.
Proof. done. Qed.

Lemma dom_spec S T (f: S ->> T): dom f === (inv_img f All).
Proof. by split => [[t] | [t []]]; exists t. Qed.

Global Instance dom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv S)) (@dom S T).
Proof. by move => f g eq s; split; move => [t]; exists t; apply (eq s t). Qed.

Lemma F2MF_dom S T (f: S -> T): dom (F2MF f) === All.
Proof. by move => s; split => // _; exists (f s). Qed.

Definition codom S T (f: S ->> T):= make_subset (fun t => exists s, f s t).
(* the codomain of a multi-valued function is the union of all its value sets. It should
not be understood as the range, as very few of its elements may be hit by a choice function. *)
Lemma codom_spec S T (f: S ->> T): codom f === (img f All).
Proof. by split => [[t] | [t []]]; exists t. Qed.

Lemma codom_crct S T (f: S ->> T) t : t \from codom f <-> exists s, f s t.
Proof. done. Qed.

Lemma codom_dom_inv S T (f: S ->> T): codom f === dom (f\^-1).
Proof. done. Qed.

Lemma inv_dom_codom S T (f: S ->> T) t:
	t \from codom f <-> t \from dom (f\^-1).
Proof. exact/ codom_dom_inv. Qed.

Global Instance codom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv T)) (@codom S T).
Proof. by move => f g eq; rewrite !codom_dom_inv eq. Qed.

Definition mf_id S:= F2MF (@id S).

Arguments mf_id {S}.

Lemma id_inv S:
	mf_id\^-1 =~=@mf_id S.
Proof. done. Qed.

Definition empty_mf S T := make_mf (fun (s: S) (t: T) => False).

Lemma empty_inv S T:
	(@empty_mf S T) \inverse =~= (@empty_mf T S).
Proof. done. Qed.

Definition corestr S T (f: S ->> T) (P: mf_subset.type T) := make_mf (fun s t => P t /\ f s t).
Notation "f '\corestricted_to' P" := (corestr f P) (at level 2).
Notation "f '|^' P" := (corestr f P) (format "f '|^' P", at level 2).

Lemma corestr_crct S T (f: S ->> T) P s t: f|^P s t <-> P t /\ f s t.
Proof. done. Qed.

Lemma corestr_spec S T (f: S ->> T) P s: (f|^P) s  === intersection P (f s).
Proof. done. Qed.

Lemma corestr_all S T (f: S ->> T): f =~= (f|^All).
Proof. by move => s t; split => // [[]]. Qed.

Global Instance corestr_prpr S T:
	Proper (@equiv S T ==> @set_equiv T ==> @equiv S T) (@corestr S T).
Proof.
move => f g feqg P Q PeqQ s t.
by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
Qed.

Definition restr S T (f: S ->> T) (P: mf_subset.type S) := make_mf (fun s t => P s /\ f s t).
Notation "f '\restricted_to' P" := (restr f P) (at level 2).
Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2).

Lemma restr_dom S T (f: S ->> T): f|_(dom f) =~= f.
Proof. by move => s t; split => [[] | fst] //; split => //; exists t. Qed.

Lemma dom_restr_spec S T (f: S ->> T) P s:
s \from dom (f|_P) <-> s \from dom f /\ P s.
Proof. by split => [[t []] | [[t]]]; first split; try by exists t. Qed.

Lemma dom_restr_subs S T (f: S ->> T) P Q:
	P \is_subset_of Q -> dom (f|_P) \is_subset_of dom (f|_Q).
Proof. by move => subs s [t [fst Pt]]; exists t; split; first apply/subs. Qed.

Lemma corestr_restr_inv S T (f: S ->> T) P: f|_P =~= ((f\^-1)|^P)\^-1.

Lemma restr_crct S T (f: S ->> T) P s t: (f \restricted_to P) s t <-> P s /\ f s t.
Proof. done. Qed.

Lemma restr_all S T (f: S ->> T): f =~= (f|_All).
Proof. by move => s t; split => // [[]]. Qed.

Global Instance restr_prpr S T: Proper (@equiv S T ==> @set_equiv S ==> @equiv S T) (@restr S T).
Proof.
move => f g feqg P Q PeqQ s t.
by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
Qed.

Lemma restr_inv S T (f: S ->> T) P: (f|_P)\^-1 =~= (f\^-1)|^P.
Proof. done. Qed.
End Basics.
Notation "f =~= g" := (equiv f g) (at level 70).
Notation inv f := (inverse f).
Notation "f '\inverse'" := (inverse f) (at level 70).
Notation "f '\^-1'" := (inverse f) (format "f '\^-1'", at level 30).
Notation "f '\corestricted_to' P" := (corestr f P) (at level 2).
Notation "f '|^' P" := (corestr f P) (format "f '|^' P", at level 2).
Notation "f '\restricted_to' P" := (restr f P) (at level 2).
Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2).
Arguments mf_id {S}.