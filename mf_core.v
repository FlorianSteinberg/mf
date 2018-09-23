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

Global Instance eqiuv_equiv S T:
	Equivalence (@equiv S T).
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

Definition mf_inv T S (f: S ->> T) := make_mf (fun t s => f s t).
Notation inv f := (mf_inv f).
Notation "f '\inverse'" := (mf_inv f) (at level 50).
Notation "f '\^-1'" := (mf_inv f) (format "f '\^-1'", at level 50).

Lemma inv_inv S T (f: S ->> T): (f\^-1)\^-1 =~= f.
Proof. done. Qed.

Global Instance inv_prpr S T: Proper ((@equiv S T) ==> (@equiv T S)) (@mf_inv T S).
Proof. by move => f g eq s t; apply (eq t s). Qed.

Definition inv_img S T (f: S ->> T) P := make_subset (fun s => intersects P (f s)).
Lemma inv_img_crct S T (f: S ->> T) P s : inv_img f P s <-> exists t, f s t /\ P t.
Proof. by split; move => [t []]; exists t. Qed.

Definition img S T (f: S ->> T) P := inv_img (inv f) P.

(* The domain of a multifunctions is the set of all inputs such that the value set
is not empty. *)
Definition dom S T (f: S ->> T) := make_subset (fun s => exists t, f s t).
Notation "s '\from_dom' f" := (dom f s) (at level 2).

Lemma dom_crct S T (f: S ->> T): dom f === (inv_img f All).
Proof. by split => [[t] | [t []]]; exists t. Qed.

Global Instance dom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv S)) (@dom S T).
Proof. by move => f g eq s; split; move => [t]; exists t; apply (eq s t). Qed.

Lemma dom_invimg S T (f: S ->> T): (dom f) === (inv_img f All).
Proof. by split => [[t fst] | [t [_ fst]]]; exists t. Qed.

Definition codom S T (f: S ->> T):= img f (@All S).
(* the codomain of a multi-valued function is the union of all its value sets. It should
not be understood as the range, as very few of its elements may be hit by a choice function. *)
Notation "t '\from_codom' f" := (codom f t) (at level 2).

Lemma codom_crct S T (f: S ->> T) t : t \from_codom f <-> exists s, f s t.
Proof. by split => [[s []] | [s]]; exists s. Qed.

Lemma codom_dom_inv S T (f: S ->> T): codom f === dom (f\^-1).
Proof. by rewrite dom_crct. Qed.

Lemma inv_dom_codom S T (f: S ->> T) t:
	t \from_codom f <-> t \from_dom (f \inverse).
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

Definition corestr S T (f: S ->> T) P := make_mf (fun s => intersection P (f s)).
Notation "f '\corestricted_to' P" := (corestr f P) (at level 2).

Lemma corestr_crct S T (f: S ->> T) P s t: (f \corestricted_to P) s t <-> P t /\ f s t.
Proof. done. Qed.

Lemma corestr_id S T (f: S ->> T): f =~= (f \corestricted_to All).
Proof. by move => s t; split => // [[]]. Qed.

Global Instance corestr_prpr S T:
	Proper (@equiv S T ==> @set_equiv T ==> @equiv S T) (@corestr S T).
Proof.
move => f g feqg P Q PeqQ s t.
by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
Qed.

Definition restr S T (f: S ->> T) P := ((f\^-1)\corestricted_to P)\^-1.
Notation "f '\restricted_to' P" := (restr f P) (at level 2).
Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2).

Lemma restr_crct S T (f: S ->> T) P s t: (f \restricted_to P) s t <-> P s /\ f s t.
Proof. done. Qed.

Lemma restr_id S T (f: S ->> T): f =~= (f \restricted_to All).
Proof. by move => s t; split => // [[]]. Qed.

Global Instance restr_prpr S T: Proper (@equiv S T ==> @set_equiv S ==> @equiv S T) (@restr S T).
Proof.
move => f g feqg P Q PeqQ s t.
by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
Qed.

Lemma restr_all S T (f: S ->> T): f|_All =~= f.
Proof. move => s t; by split => // [[]]. Qed.
End Basics.
Notation "f =~= g" := (equiv f g) (at level 70).
Notation "t '\from_codom' f" := (codom f t) (at level 2).
Notation "s '\from_dom' f" := (dom f s) (at level 2).
Notation inv f := (mf_inv f).
Notation "f '\inverse'" := (mf_inv f) (at level 70).
Notation "f '\^-1'" := (mf_inv f) (format "f '\^-1'", at level 30).
Notation "f '\corestricted_to' P" := (corestr f P) (at level 2).
Notation "f '|^' P" := (corestr f P) (format "f '|^' P", at level 2).
Notation "f '\restricted_to' P" := (restr f P) (at level 2).
Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2).
Arguments mf_id {S}.