(******************************************************************************)
(* This file provides a class of relations interpreted as multivalued         *)
(* functions. The main difference between relations and multivalued functions *)
(* is how they are composed, the composition for multivalued functions is     *)
(* Chosen such that it works well with realizability. The difference          *)
(* between multifunction and relational composition is that for the latter    *)
(* the whole image of s under f is required to be included in the domain of g *)
(* for f \o g s r to be true. Note that in ssreflect, \o is a notation for the*)
(* composition of regular functions, this notation is remapped to \o_f.       *)
(*                                                                            *)
(*            S ->> T    == The elements are functions S -> subset T.         *)
(*                          Coerced into the functions of type S -> T -> Prop *)
(*            make_mf    == Notation for the constructor mf.Pack.             *)
(*            f =~= g    == equality of multivalued functions, i.e.           *)
(*                          "forall s, f s === g s" or                        *)
(*                          "forall s t, f s t <-> g s t"                     *)
(*             F2MF      == "function to multifunction" sends a function      *)
(*                          f: S -> T to the multifunction s => singleton f s *)
(*                          i.e. F2MF f s t <-> f s = t                       *)
(*            f\^-1      == inverse multifunction, i.e. f s t <-> f\^-1 t s   *)
(*            dom f      == set of elements s such that f s is not empty.     *)
(*           codom f     == dom f\^-1                                         *)
(*             mf_id     == F2MF id i.e. mf_id s === singleton s              *)
(*           empty_mf    == constant function returning the empty set.        *)
(*             f|_A      == restriction of f to the subset A, i.e.            *)
(*                          "f|_A s = if s \from A then f s else empty"       *)
(*             f|^A      == corestriction, i.e. "f|^A = (f\^-1|_A)\^-1"       *)
(*           f \o_R g    == relational composition of f and g, i.e. of        *)
(*                          f: S ->> T and g: R ->> S, i.e. f \o_R g s r      *)
(*                          <-> forall s, exists t, f s t /\ g t r            *)
(*            f \o g     == The composition of multivalued functions          *)
(*                          i.e. if f: S ->> T and g: R ->> S, then           *)
(*                          f \o g : R ->> T and f \o g r t <->               *)
(*                          f s \is_subset_of dom g /\ f \o_R g r t           *)
(*        f \is_total    == forall s, s \from dom f or dom f === All          *)
(*                          f: S ->> T and g: R ->> S, i.e. f \o_R g s r      *)
(*                          <-> forall s, exists t, f s t /\ g t r            *)
(*      f \is_cototoal   == forall s, s \from codom f equivalent to           *)
(*                          surjectivity when f comes from a function.        *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun.
Require Import mf_set.
Require Import Morphisms.
 
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
Definition F2MF S T (f : S -> T) : (S ->> T) := make_mf (fun s => singleton (f s)).

Lemma F2MF_spec S T (f: S -> T) s t: F2MF f s t <-> f s = t.
Proof. done. Qed.

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
Proof. exact/codom_dom_inv. Qed.

Global Instance codom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv T)) (@codom S T).
Proof. by move => f g eq; rewrite !codom_dom_inv eq. Qed.

Definition mf_id S:= F2MF (@id S).

Arguments mf_id {S}.

Lemma id_inv S: mf_id\^-1 =~=@mf_id S.
Proof. done. Qed.

Definition empty_mf S T := make_mf (fun (s: S) => @empty T).

Lemma empty_inv S T: (@empty_mf S T) \inverse =~= (@empty_mf T S).
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
Proof. done. Qed.

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

Section relational_composition.
Definition mf_rel_comp R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (exists s, g r s /\ f s t)).
Notation "f '\o_R' g" := (mf_rel_comp f g) (at level 50).

Global Instance rcmp_prpr R S T:
Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_rel_comp R S T).
Proof.
move => f f' eqf g g' eqg r t.
by split; move => [s [grs fst]]; exists s; by split; [apply /eqg | apply /eqf].
Qed.

Lemma rcmp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
	((f \o_R g) \o_R h) =~= (f \o_R (g \o_R h)).
Proof.
split; last by move => [t' [[s' []]]]; exists s'; split => //; exists t'.
by move => [t' [hst [s'[]]]]; exists s'; split => //; exists t'.
Qed.

Lemma rcmp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
	(f \o_R g)\^-1 =~= (g\^-1) \o_R (f\^-1).
Proof. by move => r q'; split; move =>[q []]; exists q. Qed.

Lemma rcmp_F2MF R S T (f: S ->> T) (g: R -> S):
	(f \o_R (F2MF g)) =~= mf.Pack (fun r => f (g r)).
Proof. by move => r t /=; split => [[s [-> fst]] | fgrt]//; exists (g r). Qed.

Lemma F2MF_rcmp_F2MF R S T (f: S -> T) (g: R -> S):
	(F2MF f \o_R F2MF g) =~= F2MF (fun r => f (g r)).
Proof. by move => s t; rewrite rcmp_F2MF /=. Qed.

Lemma rcmp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
	dom (f \o_R g) \is_subset_of dom g.
Proof. by move => r [q' [q []]]; exists q. Qed.

Lemma rcmp_dom_codom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> dom f === dom (g \o_R f).
Proof.
move => dm r; split => [[t ftr] | ]; last by apply rcmp_dom.
have [ | r' gtr']:= dm t; first by exists r.
by exists r'; exists t.
Qed.

Lemma rcmp_id_restr S T (f: S ->> T) P: f \o_R mf_id|_P =~= f|_P.
Proof.
move => s t.
split; first by move => [_ [[Ps/= <-] ]].
by move => [ps fst]; exists s.
Qed.

Lemma rcmp_id_l S T (f: S ->> T):
	mf_id \o_R f =~= f.
Proof. by move => s t; split => [[t' [fst' <-]] | fst]//; exists t. Qed.

Lemma rcmp_id_r S T (f: S ->> T):
	f \o_R mf_id =~= f.
Proof. by move => s t; split => [[t' [-> fst']] | fst]//; exists s. Qed.
End relational_composition.
Notation "f '\o_R' g" := (mf_rel_comp f g) (at level 2).

Section composition.
Notation "f \o_f g" := (f \o g) (at level 30).
Definition composition R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (f \o_R g) r t /\ (g r) \is_subset_of (dom f)).
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

Section totals.
Definition total S T := make_subset (fun (f: S ->> T) => (forall s, s \from dom f)).
Notation "f \is_total" := (f \from (total _ _ )) (at level 30).

Global Instance tot_prpr S T: Proper ((@equiv S T) ==> iff) (@total S T).
Proof.
by move => f g eq; split => tot s; have [t]:= tot s; exists t; [rewrite -eq| rewrite eq].
Qed.

Context (S T S' T': Type).

Lemma tot_spec Q Q' (f: Q ->> Q'): f \is_total <-> (dom f === All).
Proof. by split => prp s; [have /=:= prp s | rewrite prp]. Qed.

Lemma rcmp_tot_dom R (f: S ->> T) (g: T ->> R):
	g \is_total -> (dom f) === (dom (g \o_R f)).
Proof.
move => tot s; split => [[t frt] | [r [t []]]]; last by exists t.
by have[r gtr]:= tot t; exists r; exists t.
Qed.

Lemma comp_tot_dom R (f: S ->> T) (g: T ->> R):
	g \is_total -> (dom f) === (dom (g \o f)).
Proof.
move => /tot_spec tot.
apply comp_dom_codom.
rewrite tot; exact/subs_all.
Qed.

Lemma comp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g \o f) \is_total.
Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -comp_tot_dom. Qed.

Lemma rcmp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g \o_R f) \is_total.
Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -rcmp_tot_dom. Qed.

Lemma tot_subs_dom R (f: S ->> T) (g: S ->> T) (h: T ->> R):
	codom g \is_subset_of dom h-> dom (h \o g) \is_subset_of dom (h \o f) -> dom g \is_subset_of dom f.
Proof.
move => tot dm s [t gst].
have [ | r [[t' []]]]:= dm s; last by exists t'.
have [ | r htr] //:= tot t; first by exists s.
by exists r; split => [ | t' gst']; [exists t | apply tot; exists s].
Qed.

Lemma F2MF_tot (f: S -> T): (F2MF f) \is_total.
Proof. by move => s; exists (f s). Qed.

(* For total multi valued functions, the relational composition is identical to the multi-
function composition.  *)
Lemma comp_rcmp R  (f : S ->> T) (g : R ->> S):
	f \is_total -> f \o g =~= f \o_R g.
Proof.
move => /tot_spec tot s t; split => [ | comp]; first by case.
by split => //; rewrite tot; exact/ subs_all.
Qed.

Definition cototal S T:= make_subset (fun (f: S ->> T) =>
	forall t, t \from codom f).
Notation "f '\is_cototal'" := (f \from (cototal _ _)) (at level 30).

Lemma cotot_spec (f: S ->> T): f \is_cototal <-> codom f === All.
Proof. by split => ass s; first split => // _; apply/ass. Qed.

Lemma cotot_tot_inv (f: S ->> T):
	f \is_cototal <-> (f \inverse) \is_total.
Proof. by rewrite cotot_spec codom_dom_inv tot_spec. Qed.
End totals.
Notation "f '\is_total'" := (f \from (total _ _)) (at level 2).
Notation "f '\is_cototal'" := (f \from (cototal _ _)) (at level 2).