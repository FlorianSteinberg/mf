(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import ClassicalChoice CRelationClasses Morphisms.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module mf_subset.
Structure type S := Pack {
P :> S -> Prop;
}.
End mf_subset.
Coercion mf_subset.P: mf_subset.type >-> Funclass.
Definition make_subset S (P: S -> Prop):= (mf_subset.Pack P).

Section mf_subsets.
Context (S: Type).
Notation set := (mf_subset.type S).

Definition set_equiv (P Q: set) := forall s, P s <-> Q s.
Notation "P === Q" := (set_equiv P Q) (at level 50).

Global Instance sqv_equiv:
	Equivalence set_equiv.
Proof.
split => // [P Q eq s | P Q R eq eq' s]; first by split => [Ps | Qs]; apply (eq s).
by split => [Ps | Rs]; [apply /eq' /eq | apply /eq /eq'].
Qed.

Notation "s \from P" := (mf_subset.P _ P s) (at level 70).

Global Instance from_prpr:
	Proper (set_equiv ==> (@eq S) ==> iff) (@mf_subset.P S).
Proof. by move => P Q eq s _ <-; apply eq. Qed.

Definition subs (P Q : set) := forall s, P s -> Q s.
Lemma subs_crct (P Q: set): subs P Q <-> subset P Q.
Proof. done. Qed.
Notation "P '\is_subset_of' Q" := (subs P Q) (at level 50).

Global Instance subs_prpr:
	Proper (set_equiv ==> set_equiv ==> iff) subs.
Proof.
by move => P Q PeQ P' Q' P'eQ'; split => subs s; intros; apply /P'eQ' /subs /PeQ.
Qed.

Lemma subs_trans (P P' P'': set):
	P \is_subset_of P' -> P' \is_subset_of P'' -> P \is_subset_of P''.
Proof. by move => PsP' P'sP'' s Ps; apply/P'sP''/PsP'. Qed.

Lemma set_eq_subs P Q:
	set_equiv  P Q <-> (P \is_subset_of Q /\ Q \is_subset_of P).
Proof.
split; first by move => eq; split => s Ps; apply eq.
move => [subs subs'] s.
split => Ps; try apply subs => //.
by apply subs'.
Qed.

Lemma set_eq_sqv (P Q: set): P \is_subset_of Q -> Q \is_subset_of P -> P === Q.
Proof. by move => subs subs' s; split; [apply subs | apply subs']. Qed.

Definition All := make_subset (fun (_: S) => True).

Lemma subs_all P: P \is_subset_of All.
Proof. done. Qed. 

Definition empty := make_subset (fun (_: S) => False).

Lemma subs_emptly P : empty \is_subset_of P.
Proof. done. Qed.

Definition intersects (P Q: set) := exists s, P s /\ Q s.
Notation "P '\intersects' Q" := (intersects P Q) (at level 50).

Lemma ntrsct_sym P Q: P \intersects Q <-> Q \intersects P.
Proof. by split; move => [s []]; exists s. Qed.

Definition intersection (P Q: set) := make_subset (fun s => P s /\ Q s).
End mf_subsets.
Notation "s \from P" := (mf_subset.P P s) (at level 70).
Notation "P === Q" := (set_equiv P Q) (at level 50).
Notation "P '\is_subset_of' Q" := (subs P Q) (at level 50).
Notation "P '\intersects' Q" := (intersects P Q) (at level 50).
Arguments All {S}.

Section products.
Definition set_prod S T (P: mf_subset.type S) (Q: mf_subset.type T) :=
	make_subset (fun st => P st.1 /\ Q st.2).
Notation "P \x Q" := (set_prod P Q) (at level 40).

Global Instance sprd_prpr S T:
	Proper (@set_equiv S ==> @set_equiv T ==> @set_equiv (S*T)) (@set_prod S T).
Proof.
move => P P' eq Q Q' eq' s /=.
by rewrite eq eq'.
Qed.

Lemma sprd_All S T (P: mf_subset.type S) (Q: mf_subset.type T):
	P === All /\ Q === All -> P \x Q === All.
Proof. by move => [eq eq'] s; rewrite eq eq'. Qed.

Lemma sprd_All_inv S T (P: mf_subset.type S) (Q: mf_subset.type T) somes somet:
	P somes -> Q somet -> P \x Q === All -> P === All /\ Q === All.
Proof.
move => Ps Qt eq.
split => [s | t]; first by have [/= _ []]//:= eq (s, somet).
by have [/= _ []]//:= eq (somes, t).
Qed.
End products.
Notation "P \x Q" := (set_prod P Q) (at level 40).