(******************************************************************************)
(* This file introduces the relational composition and proves some basic      *)
(* facts about it                                                             *)
(*             f \o_R g     == relational composition of f and g, i.e. of     *)
(*                             f: S ->> T and g: R ->> S, i.e. f \o_R g s r   *)
(*                             <-> forall s, exists t, f s t /\ g t r         *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun.
Require Import mf_set mf_core.
Require Import Morphisms.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section relational_composition.
Definition mf_rel_comp R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (exists s, g r s /\ f s t)).
Notation "f 'o_R' g" := (mf_rel_comp f g) (at level 50).

Global Instance rcmp_prpr R S T:
Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_rel_comp R S T).
Proof.
move => f f' eqf g g' eqg r t.
by split; move => [s [grs fst]]; exists s; by split; [apply /eqg | apply /eqf].
Qed.

Lemma rcmp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
	((f o_R g) o_R h) =~= (f o_R (g o_R h)).
Proof.
split; last by move => [t' [[s' []]]]; exists s'; split => //; exists t'.
by move => [t' [hst [s'[]]]]; exists s'; split => //; exists t'.
Qed.

Lemma rcmp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
	(f o_R g)\^-1 =~= (g\^-1) o_R (f\^-1).
Proof. by move => r q'; split; move =>[q []]; exists q. Qed.

Lemma rcmp_F2MF R S T (f: S ->> T) (g: R -> S):
	(f o_R (F2MF g)) =~= mf.Pack (fun r => f (g r)).
Proof. by move => r t /=; split => [[s [-> fst]] | fgrt]//; exists (g r). Qed.

Lemma F2MF_rcmp_F2MF R S T (f: S -> T) (g: R -> S):
	(F2MF f o_R F2MF g) =~= F2MF (fun r => f (g r)).
Proof. by move => s t; rewrite rcmp_F2MF /=. Qed.

Lemma rcmp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
	dom (f o_R g) \is_subset_of dom g.
Proof. by move => r [q' [q []]]; exists q. Qed.

Lemma rcmp_dom_codom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> dom f === dom (g o_R f).
Proof.
move => dm r; split => [[t ftr] | ]; last by apply rcmp_dom.
have [ | r' gtr']:= dm t; first by exists r.
by exists r'; exists t.
Qed.

Lemma rcmp_id_restr S T (f: S ->> T) P: f o_R mf_id|_P =~= f|_P.
Proof.
move => s t.
split; first by move => [_ [[Ps/= <-] ]].
by move => [ps fst]; exists s.
Qed.

Lemma rcmp_id_l S T (f: S ->> T):
	mf_id o_R f =~= f.
Proof. by move => s t; split => [[t' [fst' <-]] | fst]//; exists t. Qed.

Lemma rcmp_id_r S T (f: S ->> T):
	f o_R mf_id =~= f.
Proof. by move => s t; split => [[t' [-> fst']] | fst]//; exists s. Qed.
End relational_composition.
Notation "f 'o_R' g" := (mf_rel_comp f g) (at level 2).