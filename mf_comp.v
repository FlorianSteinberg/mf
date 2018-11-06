(******************************************************************************)
(* This file introduces the relational composition and the multi function     *)
(* composition and proves some basic facts about them. The difference to      *)
(* between multifunction and relational composition is that for the latter    *)
(* the whole image of s under f is required to be included in the domain of g *)
(* for f \o g s r to be true. This composition is more wellbehaved with       *)
(* respect to realizability. Note that in ssreflect, \o is a notation for the *)
(* composition of regular functions, this notation is remapped to \o_f.       *)
(*             f \o_R g     == relational composition of f and g, i.e. of     *)
(*                             f: S ->> T and g: R ->> S, i.e. f \o_R g s r   *)
(*                             <-> forall s, exists t, f s t /\ g t r         *)
(*             f \o g       == The composition of multivalued functions       *)
(*                             i.e. if f: S ->> T and g: R ->> S, then        *)
(*                             f \o g : R ->> T and f \o g r t <->            *)
(*                             f s \is_subset_of dom g /\ f \o_R g r t        *)
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

Section composition.
Notation "f \o_f g" := (f \o g) (at level 30).
Definition composition R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (f o_R g) r t /\ (g r) \is_subset_of (dom f)).
Notation "f '\o' g" := (composition f g) (at level 50).

Global Instance comp_prpr R S T: Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@composition R S T).
Proof.
move => f f' eqf g g' eqg s t; split; case.
	split; last by move => r g'sr; rewrite -eqf; apply/b/eqg.
	by move: a => [r stf]; exists r; rewrite -(eqf r t) -(eqg s r).
split; last by move => r g'sr; rewrite eqf; apply/b/eqg.
by move: a => [r stf]; exists r; rewrite (eqf r t) (eqg s r).
Qed.

Lemma comp_F2MF R S T (f: S ->> T) (g: R -> S):
	(f \o (F2MF g)) =~= mf.Pack (fun r => f (g r)).
Proof.
split => [[[r [/=-> fst]] prop] | fgrt] //.
by split => [ | r eq]; [exists (g s) | exists s0; rewrite -eq].
Qed.

Lemma F2MF_comp_F2MF R S T (f: S -> T) (g: R -> S):
	(F2MF f \o F2MF g) =~= F2MF (fun r => f (g r)).
Proof. by move => s t; rewrite comp_F2MF /=. Qed.

Notation "f '\is_section_of' g" := (f \o g =~= F2MF id) (at level 2).

Lemma sec_cncl S T (f: S -> T) g:
	(F2MF f) \is_section_of (F2MF g) <-> cancel g f.
Proof.
split; last by intros; rewrite comp_F2MF /F2MF => s t; split => <-.
by move => eq s; move: (eq s s); rewrite (comp_F2MF _ g _ s) /F2MF /= => ->.
Qed.

Lemma comp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
	dom (f \o g) \is_subset_of dom g.
Proof. by move => r [s [[t[]]]]; exists t. Qed.

Lemma comp_subs_dom R S T (f: S ->> T) (g: T ->> R) s:
	f s \is_subset_of dom g -> s \from dom f <-> s \from dom (g \o f).
Proof.
move => subs.
split; last by move => [r [[t [fst]]]]; exists t.
move => [t fst].
have [r gtr]:= subs t fst.
by exists r; split; first by exists t.
Qed.

Lemma comp_dom_codom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> dom f === dom (g \o f).
Proof.
move => subs s; apply /comp_subs_dom => t fst.
by apply subs; exists s.
Qed.

Lemma comp_codom R S T (f: S ->> T) (g: T ->> R):
	codom (g \o f) \is_subset_of codom g.
Proof. by move=> r /codom_crct [s] [[t [fst gtr]] _]; exists t. Qed.

Lemma comp_codom_dom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> codom g|_(codom f) === codom (g \o f).
Proof.
move => subs r.
split.
	move => /codom_crct [t [/codom_crct [s fst] gtr]].
	rewrite codom_crct; exists s.
	split => [ | t' fst']; first by exists t.
	by apply subs; exists s.
move => /codom_crct [s [[t [fst gtr]]] subs'].
by rewrite codom_crct; exists t; split; first exists s.
Qed.

(* This operation is associative *)
Lemma comp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
	((f \o g) \o h) =~= (f \o (g \o h)).
Proof.
move => r q.
split => [ [] [] s [] hrs [] [] t []| [] [] t [] [] [] s [] ].
	split => [ | t' [] [] s' [] hrs'].
		exists t;	split => //; split => [ | s' hrs']; first by exists s.
		by move: (b1 s' hrs') => [] x [] [] t' []; exists t'.
	by move: (b1 s' hrs') => [] q' comp gs't _; apply comp.2.
split => [ | s' hrs'].
	exists s; split => //.
	split => [ | t' gst']; first by exists t.
	suffices ghrs: (g \o h) r t' by apply (b2 t' ghrs).
	by split => [ | s' hrs']; [exists s | apply b0].
move: (b0 s' hrs') => [] t' gs't'.
have ghrt': (g \o h) r t'
	by split => [ | s'' hrs'']; [exists s' | apply b0].
move: (b2 t' ghrt') => [] q' ft'q'; exists q'.
split => [ | t'' gs't'']; first by exists t'.
suffices ghrt'': (g \o h) r t'' by apply b2.
by split => [ | s'' hrs'']; [exists s' | apply b0].
Qed.

Lemma comp_id_restr S T (f: S ->> T) P: f \o mf_id|_P =~= f|_P.
Proof.
by move => s t; split => [[[_ [[Ps <-]]]] | []] //; split => [ | t' [_ <-]]; [exists s | exists t].
Qed.

Lemma comp_id_l S T (f: S ->> T):
	mf_id \o f =~= f.
Proof.
split => [[[t' [fst <-]] _] | fst] //; by split => [ | t' fst']; [exists s0 | exists t'].
Qed.

Lemma comp_id_r S T (f: S ->> T):
	f \o mf_id =~= f.
Proof.
split => [[[t' [<- fst]] _] | fst] //; by split => [| t' <- ]; [exists s|exists s0].
Qed.

Lemma comp_empty_l S T R (f: S ->> T): (@empty_mf T R) \o f =~= (@empty_mf S R).
Proof. by split => //=; move => [[a []]]. Qed.

Lemma comp_empty_r S T R (f: S ->> T): f \o (@empty_mf R S) =~= (@empty_mf R T).
Proof. by split => //=; move => [[a []]]. Qed.
End composition.
Notation "f \o_f g" := (f \o g) (at level 50).
Notation "f '\o' g" := (composition f g) (at level 50).