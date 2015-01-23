(** * Hoare: Hoare Logic *)


Require Export Imp.

(** In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g. functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv] chapter). 

    If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (in some cases, even subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in the course when we discuss _types_ and _type
    soundness_.  In this chapter, though, we'll turn to a different
    set of issues.

    Our goal is to see how to carry out some simple examples of
    _program verification_ -- i.e., using the precise definition of
    Imp to prove formally that particular programs satisfy particular
    specifications of their behavior. We'll develop a reasoning system
    called _Floyd-Hoare Logic_ -- often shortened to just _Hoare
    Logic_ -- in which each of the syntactic constructs of Imp is
    equipped with a single, generic "proof rule" that can be used to
    reason compositionally about the correctness of programs involving
    this construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software
    systems. *)


  
(* ####################################################### *)
(** * Hoare Logic *)

(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that programs are correct with
    respect to such specifications -- where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. *)

(* ####################################################### *)
(** ** Assertions *)

(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when program execution
    reaches that point.  Formally, an assertion is just a family of
    propositions indexed by a [state]. *)

Definition Assertion := state -> Prop.

(** **** Exercise: 1 star, optional (assertions) *)
Module ExAssertions.

(** Paraphrase the following assertions in English. *)

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

(* FILL IN HERE *)

End ExAssertions.
(** [] *)

(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables (we will never need
    to talk about two different memory states at the same time).  For
    discussing examples informally, we'll adopt some simplifying
    conventions: we'll drop the initial [fun st =>], and we'll write
    just [X] to mean [st X].  Thus, instead of writing *)
(** 
      fun st => (st Z) * (st Z) <= x /\
                ~ ((S (st Z)) * (S (st Z)) <= x)
    we'll write just
         Z * Z <= x /\ ~((S Z) * (S Z) <= x).
*)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q] (in ASCII, [P -][>][> Q]), if, whenever [P]
    holds in some state [st], [Q] also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** We'll also have occasion to use the "iff" variant of implication
    between assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ####################################################### *)
(** ** Hoare Triples *)

(** Next, we need a way of making formal claims about the
    behavior of commands. *)

(** Since the behavior of a command is to transform one state to
    another, it is natural to express claims about commands in terms
    of assertions that are true before and after the command executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  Formally: *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
       {{P}} c {{Q}}.
*)
(** (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** **** Exercise: 1 star (triples) *)
(** Paraphrase the following Hoare triples in English.
   1) {{True}} c {{X = 5}}

   2) {{X = x}} c {{X = x + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = x}} 
      c
      {{Y = real_fact x}}.

   6) {{True}} 
      c 
      {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}

 *)


(** [] *)









(** **** Exercise: 1 star (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?
   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}

*)
(* FILL IN HERE *)
(** [] *)

(** (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability, rather than their
   formal [aexp] and [bexp] encodings.  We'll continue doing so
   throughout the chapter.) *)

(** To get us warmed up for what's coming, here are two simple
    facts about Hoare triples. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *) 
(** ** Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. We will prove programs correct using these proof rules,
    without ever unfolding the definition of [hoare_triple]. *)

(* ####################################################### *) 
(** *** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if [a] is _any_ arithmetic expression, then
       {{ a = 1 }}  X ::= a {{ X = 1 }}
    is a valid Hoare triple. 

    This can be made even more general. To conclude that an
    _arbitrary_ property [Q] holds after [X ::= a], we need to assume
    that [Q] holds before [X ::= a], but _with all occurrences of_ [X]
    replaced by [a] in [Q]. This leads to the Hoare rule for
    assignment
      {{ Q [X |-> a] }} X ::= a {{ Q }}
    where "[Q [X |-> a]]" is pronounced "[Q] where [a] is substituted
    for [X]".

    For example, these are valid applications of the assignment
    rule:
      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion."
    That is, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that, wherever [P]
    mentions [X], [P'] should instead mention [a].  
   
    Since [P] is an arbitrary Coq proposition, we can't directly
    "edit" its text.  Instead, we can achieve the effect we want by
    evaluating [P] in an updated state: *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

(** That is, [P [X |-> a]] is an assertion [P'] that is just like [P]
    except that, wherever [P] looks up the variable [X] in the current
    state, [P'] instead uses the value of the expression [a].

    To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (ANum 3))),
    which simplifies to 
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X 3)
    and further simplifies to
    fun st => 
      ((update st X 3) X) <= 5)
    and by further simplification to
    fun st => 
      (3 <= 5).
    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected).

    For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X+1]].  Formally, [P'] is the Coq expression
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (APlus (AId X) (ANum 1)))),
    which simplifies to 
    fun st => 
      (((update st X (aeval st (APlus (AId X) (ANum 1))))) X) <= 5
    and further simplifies to
    fun st => 
      (aeval st (APlus (AId X) (ANum 1))) <= 5.
    That is, [P'] is the assertion that [X+1] is at most [5].

*)

(** Now we can give the precise proof rule for assignment: 
      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.  Qed.

(** **** Exercise: 2 stars (hoare_asgn_examples) *)
(** Translate these informal Hoare triples...
    1) {{ (X <= 5) [X |-> X + 1] }}
       X ::= X + 1
       {{ X <= 5 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}
   ...into formal statements and use [hoare_asgn] to prove them. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (hoare_asgn_wrong) *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (hoare_asgn_fwd) *)
(** However, using an auxiliary variable [x] to remember the original
    value of [X] we can define a Hoare rule for assignment that does,
    intuitively, "work forwards" rather than backwards.
  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q st' /\ st X = aeval st' a }}
  (where st' = update st X x)
    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point). Also note that this
    rule is more complicated than [hoare_asgn].
*)

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y}, (forall (x: X), f x = g x) ->  f = g) ->
  forall x a Q,
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q (update st X x) /\ st X = aeval (update st X x) a }}.
Proof.
  intros functional_extensionality v a Q.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(** *** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},
    follows directly from the assignment rule, 
      {{True}} X ::= 3 {{X = 3}}.
    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We might capture this observation with the
    following rule:
                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

(** For example, we might use the first consequence rule like this:
                {{ True }} =>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Or, formally... 
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, update. simpl. reflexivity.
Qed.

(** Finally, for convenience in some proofs, we can state a "combined"
    rule of consequence that allows us to vary both the precondition
    and the postcondition. 
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ####################################################### *)
(** *** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature of
    Coq.  We had to write "[with (P' := ...)]" explicitly in the proof
    of [hoare_asgn_example1] and [hoare_consequence] above, to make
    sure that all of the metavariables in the premises to the
    [hoare_consequence_pre] rule would be set to specific
    values.  (Since [P'] doesn't appear in the conclusion of
    [hoare_consequence_pre], the process of unifying the conclusion
    with the current goal doesn't constrain [P'] to a specific
    assertion.)

    This is a little annoying, both because the assertion is a bit
    long and also because for [hoare_asgn_example1] the very next
    thing we are going to do -- applying the [hoare_asgn] rule -- will
    tell us exactly what it should be!  We can use [eapply] instead of
    [apply] to tell Coq, essentially, "Be patient: The missing part is
    going to be filled in soon." *)

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H]
    except that, instead of failing if unifying the goal with the
    conclusion of [H] does not determine how to instantiate all
    of the variables appearing in the premises of [H], [eapply H]
    will replace these variables with _existential variables_
    (written [?nnn]) as placeholders for expressions that will be
    determined (by further unification) later in the proof. *)

(** In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq
    will (rightly) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.

(** Coq gives a warning after [apply HP]:
     No more subgoals but non-instantiated existential variables:
     Existential 1 =
     ?171 : [P : nat -> nat -> Prop
             Q : nat -> Prop
             HP : forall x y : nat, P x y
             HQ : forall x y : nat, P x y -> Q x |- nat] 
   Trying to finish the proof with [Qed] gives an error:
<<
    Error: Attempt to save a proof with existential variables still
    non-instantiated
>> *)

Abort.

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing (ordinary) variables that did
    not exist at the time the existential variable was created. *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].

(** Doing [apply HP'] above fails with the following error:
     Error: Impossible to unify "?175" with "y".
    In this case there is an easy fix:
    doing [destruct HP] _before_ doing [eapply HQ].
*)

Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** In the last step we did [apply HP'] which unifies the existential
    variable in the goal with the variable [y]. The [assumption]
    tactic doesn't work in this case, since it cannot handle
    existential variables. However, Coq also provides an [eassumption]
    tactic that solves the goal if one of the premises matches the
    goal up to instantiations of existential variables. We can use
    it instead of [apply HP']. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** **** Exercise: 2 stars (hoare_asgn_examples_2) *)
(** Translate these informal Hoare triples...
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...into formal statements and use [hoare_asgn] and
   [hoare_consequence_pre] to prove them. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *) 
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)

(** Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H. subst. reflexivity. Qed.

(** You will most often use [hoare_seq] and
    [hoare_consequence_pre] in conjunction with the [eapply] tactic,
    as done above. *)

(** **** Exercise: 2 stars (hoare_asgn_example4) *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  apply hoare_seq with (Q := fun st => st X = 1).
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. split. assumption. reflexivity.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. reflexivity.
Qed.
  
(*
  intros st H.
  split.
  inversion H0; subst.
  inversion H7; subst.
  inversion H4; subst. reflexivity.
  inversion H0; subst.
  inversion H7; subst. reflexivity.
Qed.
*)

(** **** Exercise: 3 stars (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
      {{X <= Y}} c {{Y <= X}}
*)

Definition swap_program : com :=
  (* FILL IN HERE *) admit.

Theorem swap_exercise :
  {{fun st => st X <= st Y}} 
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (hoarestate1) *)
(** Explain why the following proposition can't be proven:
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3); Y ::= a)
         {{fun st => st Y = n}}.
*)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   However, this is rather weak. For example, using this rule,
   we cannot show that:
     {{ True }} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches.
   
   But we can actually say something more precise.  In the "then"
   branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the rule gives
   us more information to work with when reasoning about the behavior
   of [c1] and [c2] (i.e., the reasons why they establish the
   postcondition [Q]).
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update, assert_implies.
    simpl. intros st [_ H].
    symmetry in H; apply beq_nat_eq in H.
    rewrite H. omega.
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** Exercise: 2 stars (if_minus_plus) *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  apply hoare_if.
  Case "true".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn. unfold assn_sub. unfold assert_implies.
    simpl. intros. inversion H. unfold update. simpl.
    apply ble_nat_true in H1. omega.
  Case "false".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn. unfold assn_sub. unfold assert_implies.
    simpl. intros. inversion H. unfold update; simpl.
    reflexivity.
Qed.

(* ####################################################### *)
(** *** Exercise: One-sided conditionals *)

(** **** Exercise: 4 stars (if1_hoare) *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)


(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" := 
  (CIf1 b c) (at level 80, right associativity).

(** Next we need to extend the evaluation relation to accommodate
    [IF1] branches.  This is for you to do... What rule(s) need to be
    added to [ceval] to evaluate one-sided conditionals? *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
(* FILL IN HERE *)

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  (* FILL IN HERE *)
  ].

(** Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Finally, we (i.e., you) need to state and prove a theorem,
    [hoare_if1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, prove formally that your rule is precise enough
    to show the following valid Hoare triple:
  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)


Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If1.
(** [] *)

(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops.  Suppose
    we have a loop
      WHILE b DO c END
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
      {{P}} WHILE b DO c END {{Q}} 
    is a valid triple. *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write
      {{P}} WHILE b DO c END {{P}}.
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
      {{P}} WHILE b DO c END {{P /\ ~b}}
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_.

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the rule:
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)




Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst.

  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn, assn_sub, assert_implies, update. simpl.
    intros st [H1 H2]. apply ble_nat_true in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb]. 
    simpl in Hb. remember (ble_nat (st X) 2) as le. destruct le. 
    apply ex_falso_quodlibet. apply Hb; reflexivity.  
    symmetry in Heqle. apply ble_nat_false in Heqle. omega. 
Qed.

(** We can also use the while rule to prove the following Hoare
    triple, which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Actually, this result shouldn't be surprising.  If we look back at
    the definition of [hoare_triple], we can see that it asserts
    something meaningful _only_ when the command terminates. *)

Print hoare_triple.

(** If the command doesn't terminate, we can prove anything we like
    about the post-condition.  Here's a more direct proof of the same
    fact: *)

Theorem always_loop_hoare' : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.  
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra. 
Qed.

(** Hoare rules that only talk about terminating commands are often
    said to describe a logic of "partial" correctness.  It is also
    possible to give Hoare rules for "total" correctness, which build
    in the fact that the commands terminate. However, in this course
    we will focus only on partial correctness. *)

(* ####################################################### *)
(** *** Exercise: [REPEAT] *)

Module RepeatExercise.

(** **** Exercise: 4 stars (hoare_repeat) *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* FILL IN HERE *)
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
  | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
(* FILL IN HERE *)
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state ||
               update (update empty_state X 1) Y 1.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following _valid_ Hoare triple:
  {{ X > 0 }}
  REPEAT
    Y ::= X;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)


End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Exercise: [HAVOC] *)

(** **** Exercise: 3 stars (himp_hoare) *)

(** In this exercise, we will derive proof rules for the [HAVOC] command
    which we studied in the last chapter. First, we enclose this work
    in a separate module, and recall the syntax and big-step semantics
    of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st || update st X n

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

(** The definition of Hoare triples is exactly as before. Unlike our
    notion of program equivalence, which had subtle consequences with
    occassionally nonterminating commands (exercise [havoc_diverge]),
    this definition is still fully satisfactory. Convince yourself of
    this before proceeding. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
(* FILL IN HERE *) admit.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.
(** [] *)


(* ####################################################### *)
(** * Review of Hoare Logic *)

(** Above, we've introduced Hoare Logic as a tool to reasoning
    about Imp programs. In the reminder of this chapter we will
    explore a systematic way to use Hoare Logic to prove properties
    about programs. The rules of Hoare Logic are the following: *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
    Next we'll see how these rules are used to prove that programs
    satisfy specifications of their behavior.
*)


(* ####################################################### *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _compositional_ --
    the structure of proofs exactly follows the structure of programs.
    This suggests that we can record the essential ideas of a proof
    informally (leaving out some low-level calculational details) by
    decorating programs with appropriate assertions around each
    statement.  Such a _decorated program_ carries with it
    an (informal) proof of its own correctness. *)

(** For example, here is a complete decorated program: *)
(**
      {{ True }} ->>
      {{ x = x }}
    X ::= x; 
      {{ X = x }} ->> 
      {{ X = x /\ z = z }}
    Z ::= z;              
      {{ X = x /\ Z = z }} ->>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} ->>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;               
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1 
        {{ Z - X = z - x }} 
    END;
      {{ Z - X = z - x /\ ~ (X <> 0) }} ->>
      {{ Z = z - x }} ->>
      {{ Z + 1 = z - x + 1 }}
    Z ::= Z + 1
      {{ Z = z - x + 1 }}
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions.  To check that a decorated program
    represents a valid proof, we check that each individual command is
    _locally_ consistent with its accompanying assertions in the
    following sense: *)

(** 
    - [SKIP] is locally consistent if its precondition and
      postcondition are the same:
          {{ P }} 
          SKIP
          {{ P }} 
    - The sequential composition of commands [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1] is
      locally consistent (with respect to [P] and [Q]) and [c2] is
      locally consistent (with respect to [Q] and [R]):
          {{ P }} 
          c1;
          {{ Q }} 
          c2
          {{ R }}

    - An assignment is locally consistent if its precondition is
      the appropriate substitution of its postcondition:
          {{ P where a is substituted for X }}  
          X ::= a  
          {{ P }}
    - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P /\ b] and [P /\ ~b] and if its "then"
      branch is locally consistent (with respect to [P /\ b] and [Q])
      and its "else" branch is locally consistent (with respect to
      [P /\ ~b] and [Q]):
          {{ P }} 
          IFB b THEN
            {{ P /\ b }} 
            c1 
            {{ Q }}
          ELSE
            {{ P /\ ~b }} 
            c2
            {{ Q }}
          FI
          {{ Q }}

    - A while loop with precondition [P] is locally consistent if its
      postcondition is [P /\ ~b] and if the pre- and postconditions of
      its body are exactly [P /\ b] and [P]:
          {{ P }} 
          WHILE b DO
            {{ P /\ b }} 
            c1 
            {{ P }}
          END
          {{ P /\ ~b }} 

    - A pair of assertions separated by [->>] is locally consistent if
      the first implies the second (in all states):
          {{ P }} ->>
          {{ P' }} 

      This corresponds to the application of [hoare_consequence] and
      is the only place in a decorated program where checking if
      decorations are correct is not fully mechanical and syntactic,
      but involves logical and/or arithmetic reasoning.
*)

(** We have seen above how _verifying_ the correctness of a given
    proof involves checking that every single command is locally
    consistent with the accompanying assertions.  If we are instead
    interested in _finding_ a proof for a given specification we need
    to discover the right assertions. This can be done in an almost
    automatic way, with the exception of finding loop invariants,
    which is the subject of in the next section.  In the reminder of
    this section we explain in detail how to construct decorations for
    several simple programs that don't involve non-trivial loop
    invariants. *)

(* ####################################################### *)
(** ** Example: Swapping Using Addition and Subtraction *)

(** Here is a program that swaps the values of two variables using
    addition and subtraction.
  X ::= X + Y;
  Y ::= X - Y;
  X ::= X - Y
    We can prove using decorations that this program is correct --
    i.e., it always swaps the values of variables [X] and [Y].
 (1)     {{ X = x /\ Y = y }} ->>
 (2)     {{ (X + Y) - ((X + Y) - Y) = y /\ (X + Y) - Y = x }}
        X ::= X + Y;
 (3)     {{ X - (X - Y) = y /\ X - Y = x }}
        Y ::= X - Y;
 (4)     {{ X - Y = y /\ Y = x }}
        X ::= X - Y
 (5)     {{ X = y /\ Y = x }}
    The decorations were constructed as follows:
      - We begin with the undecorated program (the unnumbered lines).
      - We then add the specification -- i.e., the outer
        precondition (1) and postcondition (5). In the precondition we
        use auxiliary variables (parameters) [x] and [y] to remember
        the initial values of variables [X] and respectively [Y], so
        that we can refer to them in the postcondition (5).
      - We work backwards mechanically starting from (5) all the way
        to (2). At each step, we obtain the precondition of the
        assignment from its postcondition by substituting the assigned
        variable with the right-hand-side of the assignment. For
        instance, we obtain (4) by substituting [X] with [X - Y]
        in (5), and (3) by substituting [Y] with [X - Y] in (4).
      - Finally, we verify that (1) logically implies (2) -- i.e.,
        that the step from (1) to (2) is a valid use of the law of
        consequence. For this we substitute [X] by [x] and [Y] by [y]
        and calculate as follows:
            (x + y) - ((x + y) - y) = y /\ (x + y) - y = x
            (x + y) - x = y /\ x = x
            y = y /\ x = x

    (Note that, since we are working with natural numbers, not
    fixed-size machine integers, we don't need to worry about the
    possibility of arithmetic overflow anywhere in this argument.)
*)

(* ####################################################### *)
(** ** Example: Simple Conditionals *)

(** Here is a simple decorated program using conditionals:
 (1)     {{True}}
       IFB X <= Y THEN
 (2)       {{True /\ X <= Y}} ->>
 (3)       {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
         Z ::= AMinus (AId Y) (AId X)
 (4)       {{Z + X = Y \/ Z + Y = X}} 
       ELSE
 (5)       {{True /\ ~(X <= Y) }} ->>
 (6)       {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
         Z ::= AMinus (AId X) (AId Y)
 (7)       {{Z + X = Y \/ Z + Y = X}}
       FI
 (8)     {{Z + X = Y \/ Z + Y = X}}

These decorations were constructed as follows:
  - We start with the outer precondition (1) and postcondition (8).
  - We follow the format dictated by the [hoare_if] rule and copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).
  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).
  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~(X <= Y)] ensures that subtracting [Y] from [X] and
    then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)

(** **** Exercise: 2 stars (if_minus_plus_reloaded) *)
(** Fill in valid decorations for the following program:
   {{ True }}
  IFB X <= Y THEN
      {{                         }} ->>
      {{                         }}
    Z ::= Y - X
      {{                         }}
  ELSE
      {{                         }} ->>
      {{                         }}
    Y ::= X + Z
      {{                         }}
  FI
    {{ Y = X + Z }}
*)


(* ####################################################### *)
(** ** Example: Reduce to Zero (Trivial Loop) *)

(** Here is a [WHILE] loop that is so simple it needs no
    invariant (i.e., the invariant [True] will do the job).
 (1)      {{ True }}
        WHILE X <> 0 DO
 (2)        {{ True /\ X <> 0 }} ->>
 (3)        {{ True }}
          X ::= X - 1
 (4)        {{ True }}
        END
 (5)      {{ True /\ X = 0 }} ->>
 (6)      {{ X = 0 }}
The decorations can be constructed as follows:
  - Start with the outer precondition (1) and postcondition (6).
  - Following the format dictated by the [hoare_while] rule, we copy
    (1) to (4). We conjoin (1) with the guard to obtain (2) and with
    the negation of the guard to obtain (5). Note that, because the
    outer postcondition (6) does not syntactically match (5), we need a
    trivial use of the consequence rule from (5) to (6).
  - Assertion (3) is the same as (4), because [X] does not appear in
    [4], so the substitution in the assignment rule is trivial.
  - Finally, the implication between (2) and (3) is also trivial.
*)

(** From this informal proof, it is easy to read off a _formal_ proof
    in terms of the Hoare rules: *)

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' : 
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  (* Note that we do NOT unfold the definition of hoare_triple
     anywhere in this proof! The goal is to use only the Hoare
     rules. *)
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    (* Need to massage precondition before [hoare_asgn] applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. apply I.
  Case "Invariant and negated guard imply postcondition".
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* SearchAbout helps to find the right lemmas *)
    SearchAbout [not true]. 
    rewrite not_true_iff_false in GuardFalse. 
    SearchAbout [negb false]. 
    rewrite negb_false_iff in GuardFalse.
    SearchAbout [beq_nat true]. 
    apply beq_nat_true in GuardFalse.
    apply GuardFalse. Qed.

(* ####################################################### *)
(** ** Example: Division *)


(** The following Imp program calculates the integer division and
    remainder of two numbers [a] and [b] that are arbitrary constants
    in the program.
  X ::= a;
  Y ::= 0;
  WHILE b <= X DO
    X ::= X - b;
    Y ::= Y + 1
  END;
    In other words, if we replace [a] and [b] by concrete numbers and
    execute the program, it will terminate with the variable [X] set
    to the remainder when [a] is divided by [b] and [Y] set to the
    quotient.

    In order to give a specification to this program we need to
    remember that dividing [a] by [b] produces a reminder [X] and a
    quotient [Y] so that [b * Y + X = a /\ X > b]. It turns out that
    we get lucky with this program and don't have to think very hard
    about the loop invariant: the invariant is the just first conjunct
    [b * Y + X = a], so we use that to decorate the program.

 (1)    {{ True }} ->>
 (2)    {{ b * 0 + a = a }}
      X ::= a;
 (3)    {{ b * 0 + X = a }}
      Y ::= 0;
 (4)    {{ b * Y + X = a }}
      WHILE b <= X DO
 (5)      {{ b * Y + X = a /\ b <= X }} ->>
 (6)      {{ b * (Y + 1) + (X - b) = a }} 
        X ::= X - b;
 (7)      {{ b * (Y + 1) + X = a }}
        Y ::= Y + 1
 (8)      {{ b * Y + X = a }}
      END
 (9)    {{ b * Y + X = a /\ X < b }}

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the invariant and the loop's guard. Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8) to
    (6). Assertions (4), (3), and (2) are again backwards applications
    of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the two uses of the consequence rule are correct -- i.e., that (1)
    implies (2) and that (5) implies (6).  This is indeed the case, so
    we have a valid decorated program.
*)

(* ####################################################### *)
(** * Finding Loop Invariants *)

(** Once the outermost precondition and postcondition are chosen, the
    only creative part in verifying programs with Hoare Logic is
    finding the right loop invariants.  The reason this is difficult
    is the same as the reason that doing inductive mathematical proofs
    requires creativity: strengthening the loop invariant (or the
    induction hypothesis) means that you have a stronger assumption to
    work with when trying to establish the postcondition of the loop
    body (complete the induction step of the proof), but it also means
    that the loop body postcondition itself is harder to prove!

    This section is dedicated to teaching you how to approach the
    challenge of finding loop invariants using a series of examples
    and exercises. *)

(** ** Example: Slow Subtraction *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y]. We want to verify its
    correctness with respect to the following specification:
             {{ X = x /\ Y = y }}
           WHILE X <> 0 DO
             Y ::= Y - 1;
             X ::= X - 1
           END
             {{ Y = y - x }}

    To verify this program we need to find an invariant [I] for the
    loop. As a first step we can leave [I] as an unknown and build a
    _skeleton_ for the proof by applying backward the rules for local
    consistency. This process leads to the following skeleton:
    (1)      {{ X = x /\ Y = y }}  ->>     (a)
    (2)      {{ I }}
           WHILE X <> 0 DO
    (3)        {{ I /\ X <> 0 }}  ->>      (c)
    (4)        {{ I[X |-> X-1][Y |-> Y-1] }}
             Y ::= Y - 1;
    (5)        {{ I[X |-> X-1] }}
             X ::= X - 1
    (6)        {{ I }}
           END
    (7)      {{ I /\ X = 0 }}  ->>         (b)
    (8)      {{ Y = y - x }}

    By examining this skeleton, we can see that any valid [I] will
    have to respect three conditions:
    - (a) it must be weak enough to be implied by the loop's
      precondition, i.e. (1) must imply (2);
    - (b) it must be strong enough to imply the loop's postcondition,
      i.e. (7) must imply (8);
    - (c) it must be preserved by one iteration of the loop, i.e. (3)
      must imply (4). *)


(** These conditions are actually independent of the particular
    program and specification we are considering. Indeed, every loop
    invariant has to satisfy them. One way to find an invariant that
    simultaneously satisfies these three conditions is by using an
    iterative process: start with a "candidate" invariant (e.g. a
    guess or a heuristic choice) and check the three conditions above;
    if any of the checks fails, try to use the information that we get
    from the failure to produce another (hopefully better) candidate
    invariant, and repeat the process.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [True] as an invariant did the
    job. So let's try it again here!  I.e., let's instantiate [I] with
    [True] in the skeleton above see what we get...
    (1)      {{ X = x /\ Y = y }} ->>       (a - OK)
    (2)      {{ True }}
           WHILE X <> 0 DO
    (3)        {{ True /\ X <> 0 }}  ->>    (c - OK)
    (4)        {{ True }}
             Y ::= Y - 1;
    (5)        {{ True }}
             X ::= X - 1
    (6)        {{ True }}
           END
    (7)      {{ True /\ X = 0 }}  ->>       (b - WRONG!)
    (8)      {{ Y = y - x }}

    While conditions (a) and (c) are trivially satisfied,
    condition (b) is wrong, i.e. it is not the case that (7) [True /\
    X = 0] implies (8) [Y = y - x].  In fact, the two assertions are
    completely unrelated and it is easy to find a counterexample (say,
    [Y = X = x = 0] and [y = 1]).

    If we want (b) to hold, we need to strengthen the invariant so
    that it implies the postcondition (8).  One very simple way to do
    this is to let the invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [I] with [Y = y - x], and
    check conditions (a) to (c) again.
    (1)      {{ X = x /\ Y = y }}  ->>          (a - WRONG!)
    (2)      {{ Y = y - x }}
           WHILE X <> 0 DO
    (3)        {{ Y = y - x /\ X <> 0 }}  ->>   (c - WRONG!)
    (4)        {{ Y - 1 = y - x }}
             Y ::= Y - 1;
    (5)        {{ Y = y - x }}
             X ::= X - 1
    (6)        {{ Y = y - x }}
           END
    (7)      {{ Y = y - x /\ X = 0 }}  ->>      (b - OK)
    (8)      {{ Y = y - x }}

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [X = x /\ Y = y]
    implies (2) [Y = y - x].  If we substitute [X] by [x] we have to
    show that [x = y - x] for arbitrary [x] and [y], which does not
    hold (for instance, when [x = y = 1]).  Condition (c) requires that
    [y - x - 1 = y - x], which fails, for instance, for [y = 1] and [x =
    0]. So, although [Y = y - x] holds at the end of the loop, it does
    not hold from the start, and it doesn't hold on each iteration;
    it is not a correct invariant.

    This failure is not very surprising: the variable [Y] changes
    during the loop, while [x] and [y] are constant, so the assertion
    we chose didn't have much chance of being an invariant!  To do
    better, we need to generalize (8) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero.  Looking at how the loop
    works, we can observe that [X] and [Y] are decremented together
    until [X] reaches [0].  So, if [X = 2] and [Y = 5] initially,
    after one iteration of the loop we obtain [X = 1] and [Y = 4];
    after two iterations [X = 0] and [Y = 3]; and then the loop stops.
    Notice that the difference between [Y] and [X] stays constant
    between iterations; initially, [Y = y] and [X = x], so this
    difference is always [y - x].  So let's try instantiating [I] in
    the skeleton above with [Y - X = y - x].
    (1)      {{ X = x /\ Y = y }}  ->>               (a - OK)
    (2)      {{ Y - X = y - x }}
           WHILE X <> 0 DO
    (3)        {{ Y - X = y - x /\ X <> 0 }}  ->>    (c - OK)
    (4)        {{ (Y - 1) - (X - 1) = y - x }}
             Y ::= Y - 1;
    (5)        {{ Y - (X - 1) = y - x }}
             X ::= X - 1
    (6)        {{ Y - X = y - x }}
           END
    (7)      {{ Y - X = y - x /\ X = 0 }}  ->>       (b - OK)
    (8)      {{ Y = y - x }}

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that [X <>
    0], we have [Y - X = (Y - 1) - (X - 1)]; this holds for all
    natural numbers [X] and [Y].) *)

(* ####################################################### *)
(** ** Exercise: Slow Assignment *)

(** **** Exercise: 2 stars (slow_assignment) *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = x }}
    Y ::= 0;
    WHILE X <> 0 DO
      X ::= X - 1;
      Y ::= Y + 1;
    END
      {{ Y = x }}
    Write an informal decorated program showing that this is correct. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow Addition *)


(** **** Exercise: 3 stars, optional (add_slowly_decoration) *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Example: Parity *)


(** Here is a cute little program for computing the parity of the
    value initially stored in [X] (due to Daniel Cristofani).
    {{ X = x }}
  WHILE 2 <= X DO
    X ::= X - 2
  END
    {{ X = parity x }}
    The mathematical [parity] function used in the specification is
    defined in Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(** The postcondition does not hold at the beginning of the loop,
    since [x = parity x] does not hold for an arbitrary [x], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e. it is invariant.  The initial
    value of [X] is [x], so the parity of [X] is always equal to the
    parity of [x]. Using [parity X = parity x] as an invariant we
    obtain the following decorated program:
    {{ X = x }} ->>                              (a - OK)
    {{ parity X = parity x }}
  WHILE 2 <= X DO
      {{ parity X = parity x /\ 2 <= X }}  ->>    (c - OK)
      {{ parity (X-2) = parity x }}
    X ::= X - 2
      {{ parity X = parity x }}
  END
    {{ parity X = parity x /\ X < 2 }}  ->>       (b - OK)
    {{ X = parity x }}

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)


(** **** Exercise: 3 stars, optional (parity_formal) *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You might find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    apply ex_falso_quodlibet. apply H. omega.
Qed.

Theorem parity_correct : forall x,
    {{ fun st => st X = x }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity x }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(** ** Example: Finding Square Roots *)


(** The following program computes the square root of [X]
    by naive iteration:
      {{ X=x }}
    Z ::= 0;
    WHILE (Z+1)*(Z+1) <= X DO
      Z ::= Z+1
    END
      {{ Z*Z<=x /\ x<(Z+1)*(Z+1) }}

    As above, we can try to use the postcondition as a candidate
    invariant, obtaining the following decorated program:
 (1)  {{ X=x }}  ->>           (a - second conjunct of (2) WRONG!)
 (2)  {{ 0*0 <= x /\ x<1*1 }} 
    Z ::= 0;
 (3)  {{ Z*Z <= x /\ x<(Z+1)*(Z+1) }}
    WHILE (Z+1)*(Z+1) <= X DO
 (4)    {{ Z*Z<=x /\ (Z+1)*(Z+1)<=X }}  ->>           (c - WRONG!)
 (5)    {{ (Z+1)*(Z+1)<=x /\ x<(Z+2)*(Z+2) }} 
      Z ::= Z+1
 (6)    {{ Z*Z<=x /\ x<(Z+1)*(Z+1) }}
    END
 (7)  {{ Z*Z<=x /\ x<(Z+1)*(Z+1) /\ X<(Z+1)*(Z+1) }}  ->> (b - OK)
 (8)  {{ Z*Z<=x /\ x<(Z+1)*(Z+1) }}

    This didn't work very well: both conditions (a) and (c) failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [x]. But note that [X] is never
    assigned in this program, so we should have [X=x], but we didn't
    propagate this information from (1) into the loop invariant.
    Looking at the second conjunct of (8), it seems quite hopeless as
    an invariant -- and we don't even need it, since we can obtain it
    from the negation of the guard (third conjunct in (7)), again
    under the assumption that [X=x].  So we now try [X=x /\ Z*Z <= x]
    as the loop invariant:
      {{ X=x }}  ->>                                      (a - OK)
      {{ X=x /\ 0*0 <= x }}
    Z ::= 0;
      {{ X=x /\ Z*Z <= x }}
    WHILE (Z+1)*(Z+1) <= X DO
        {{ X=x /\ Z*Z<=x /\ (Z+1)*(Z+1)<=X }}  ->>        (c - OK)
        {{ X=x /\ (Z+1)*(Z+1)<=x }} 
      Z ::= Z+1
        {{ X=x /\ Z*Z<=x }} 
    END
      {{ X=x /\ Z*Z<=x /\ X<(Z+1)*(Z+1) }}  ->>           (b - OK)
      {{ Z*Z<=x /\ x<(Z+1)*(Z+1) }}

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied. 

    Very often, if a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop) it is necessary
    to add the fact that it doesn't change to the loop invariant. *)

(* ####################################################### *)
(** ** Example: Squaring *)


(** Here is a program that squares [X] by repeated addition:

  {{ X = x }}
  Y ::= 0;
  Z ::= 0;
  WHILE  Y  <>  X  DO
    Z ::= Z + X;
    Y ::= Y + 1
  END
  {{ Z = x*x }}
    The first thing to note is that the loop reads [X] but doesn't
    change its value. As we saw in the previous example, in such cases
    it is a good idea to add [X = x] to the invariant. The other thing
    we often use in the invariant is the postcondition, so let's add
    that too, leading to the invariant candidate [Z = x * x /\ X = x].
      {{ X = x }} ->>                            (a - WRONG)
      {{ 0 = x*x /\ X = x }}
    Y ::= 0;
      {{ 0 = x*x /\ X = x }}
    Z ::= 0;
      {{ Z = x*x /\ X = x }}
    WHILE Y <> X DO
        {{ Z = Y*x /\ X = x /\ Y <> X }} ->>     (c - WRONG)
        {{ Z+X = x*x /\ X = x }}
      Z ::= Z + X;
        {{ Z = x*x /\ X = x }}
      Y ::= Y + 1
        {{ Z = x*x /\ X = x }}
    END
      {{ Z = x*x /\ X = x /\ Y = X }} ->>         (b - OK)
      {{ Z = x*x }}

    Conditions (a) and (c) fail because of the [Z = x*x] part.  While
    [Z] starts at [0] and works itself up to [x*x], we can't expect
    [Z] to be [x*x] from the start.  If we look at how [Z] progesses
    in the loop, after the 1st iteration [Z = x], after the 2nd
    iteration [Z = 2*x], and at the end [Z = x*x].  Since the variable
    [Y] tracks how many times we go through the loop, we derive the
    new invariant candidate [Z = Y*x /\ X = x].
      {{ X = x }} ->>                               (a - OK)
      {{ 0 = 0*x /\ X = x }}
    Y ::= 0;
      {{ 0 = Y*x /\ X = x }}
    Z ::= 0;
      {{ Z = Y*x /\ X = x }}
    WHILE Y <> X DO
        {{ Z = Y*x /\ X = x /\ Y <> X }} ->>        (c - OK)
        {{ Z+X = (Y+1)*x /\ X = x }}
      Z ::= Z + X;
        {{ Z = (Y+1)*x /\ X = x }}
      Y ::= Y + 1
        {{ Z = Y*x /\ X = x }}
    END
      {{ Z = Y*x /\ X = x /\ Y = X }} ->>           (b - OK)
      {{ Z = x*x }}

    This new invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [Z = x*x] and the [Z =
    Y*x] conjunct of the invariant. It is often the case that one has
    to replace auxiliary variabes (parameters) with variables -- or
    with expressions involving both variables and parameters (like
    [x - Y]) -- when going from postconditions to invariants. *)

(* ####################################################### *)
(** ** Exercise: Factorial *)

(** **** Exercise: 3 stars (factorial) *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = x }} ;
  Y ::= 1
  WHILE X <> 0
  DO
     Y ::= Y * X
     X ::= X - 1
  END
    {{ Y = x! }}

    Fill in the blanks in following decorated program:
    {{ X = x }} ->>
    {{                                      }}
  Y ::= 1;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;
       {{                                      }}
     X ::= X - 1
       {{                                      }} 
  END
    {{                                      }} ->>
    {{ Y = x! }}
*)


(* ####################################################### *)
(** ** Exercise: Two Loops *)


(** **** Exercise: 3 stars (two_loops) *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;
  Y ::= 0;
  Z ::= c;
  WHILE X <> a DO
    X ::= X + 1;
    Z ::= Z + 1
  END;
  WHILE Y <> b DO
    Y ::= Y + 1;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;
    {{                                        }}
  Y ::= 0;
    {{                                        }}
  Z ::= c;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)


(* ####################################################### *)
(** ** Exercise: Power Series *)


(** **** Exercise: 4 stars, optional (dpow2_down) *)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^x = 2^(x+1) - 1]
  X ::= 0;
  Y ::= 1;
  Z ::= 1;
  WHILE X <> x DO
    Z ::= 2 * Z;
    Y ::= Y + Z;
    X ::= X + 1;
  END
    Write a decorated program for this. *)

(* FILL IN HERE *)


(* ####################################################### *) 
(** * Weakest Preconditions (Advanced) *)

(** Some Hoare triples are more interesting than others.
    For example,
      {{ False }}  X ::= Y + 1  {{ X <= 5 }}
    is _not_ very interesting: although it is perfectly valid, it
    tells us nothing useful.  Since the precondition isn't satisfied
    by any state, it doesn't describe any situations where we can use
    the command [X ::= Y + 1] to achieve the postcondition [X <= 5].

    By contrast, 
      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}
    is useful: it tells us that, if we can somehow create a situation
    in which we know that [Y <= 4 /\ Z = 0], then running this command
    will produce a state satisfying the postcondition.  However, this
    triple is still not as useful as it could be, because the [Z = 0]
    clause in the precondition actually has nothing to do with the
    postcondition [X <= 5].  The _most_ useful triple (for a given
    command and postcondition) is this one:
      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}
    In other words, [Y <= 4] is the _weakest_ valid precondition of
    the command [X ::= Y + 1] for the postcondition [X <= 5]. *)
 
(** In general, we say that "[P] is the weakest precondition of
    command [c] for postcondition [Q]" if [{{P}} c {{Q}}] and if,
    whenever [P'] is an assertion such that [{{P'}} c {{Q}}], we have
    [P' st] implies [P st] for all states [st].  *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** That is, [P] is the weakest precondition of [c] for [Q]
    if (a) [P] _is_ a precondition for [Q] and [c], and (b) [P] is the
    _weakest_ (easiest to satisfy) assertion that guarantees [Q] after
    executing [c]. *)

(** **** Exercise: 1 star, advanced (wp) *)
(** What are the weakest preconditions of the following commands
   for the following postconditions?
  1) {{ ? }}  SKIP  {{ X = 5 }}

  2) {{ ? }}  X ::= Y + Z {{ X = 5 }}

  3) {{ ? }}  X ::= Y  {{ X = Y }}

  4) {{ ? }}  
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

  5) {{ ? }}  
     X ::= 5
     {{ X = 0 }}

  6) {{ ? }}  
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal) *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest) *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (hoare_havoc_weakest) *)
(** Show that your [havoc_pre] rule from the [himp_hoare] exercise
    above returns the weakest precondition. *)
Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : id),
  {{ P }} HAVOC X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.
End Himp2.
(** [] *)

(* ####################################################### *)
(** * Formal Decorated Programs (Advanced) *)

(** The informal conventions for decorated programs amount to a way of
    displaying Hoare triples in which commands are annotated with
    enough embedded assertions that checking the validity of the
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.  In this section, we
    show that this informal presentation style can actually be made
    completely formal and indeed that checking the validity of
    decorated programs can mostly be automated.  *)

(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands _decorated commands_, or [dcom]s. *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}" 
      := (DCSkip P) 
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" 
      := (DCAsgn l a P) 
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" 
      := (DCWhile b Pbody d Ppost) 
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}" 
      := (DCIf b P d P' d' Q) 
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d) 
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d" 
      := (DCPre P d) 
      (at level 90)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P) 
      (at level 80, right associativity)  : dcom_scope.
Notation " d ; d' " 
      := (DCSeq d d') 
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

(** To avoid clashing with the existing [Notation] definitions
    for ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we wrap examples with the
    declaration [% dcom] to signal that we want the notations to be
    interpreted in this scope.  

    Careful readers will note that we've defined two notations for the
    [DCPre] constructor, one with and one without a [->>].  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. *)

Example dec_while : dcom := (
  {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0))) 
  DO
    {{ fun st => True /\ st X <> 0}}
    X ::= (AMinus (AId X) (ANum 1)) 
    {{ fun _ => True }}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}
) % dcom.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ; extract d2) 
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

(** The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!  

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded in [d]

       - The _pre_-condition is supplied by the context. *)

(** In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(** We can define a similar function that extracts the "initial
    precondition" from a decorated program. *)

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn X a Q            => fun st => True
  | DCIf  _ _ t _ e _       => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

(** This function is not doing anything sophisticated like calculating
    a weakest precondition; it just recursively searches for an
    explicit annotation at the very beginning of the program,
    returning default answers for programs that lack an explicit
    precondition (like a bare assignment or [SKIP]).  

    Using [pre] and [post], and assuming that we adopt the convention
    of always supplying an explicit precondition annotation at the
    very beginning of our decorated programs, we can express what it
    means for a decorated program to be correct as follows: *)

Definition dec_correct (d:dcom) := 
  {{pre d}} (extract d) {{post d}}.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus add up to a complete
    proof of correctness. *)

(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid.  It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.
    (Strictly speaking, we need to massage the informal rules a little
    bit to add some uses of the rule of consequence, but the
    correspondence should be clear.) *)

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          => 
      (P ->> Q)
  | DCSeq d1 d2      => 
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q      =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
      /\ (Q <<->> post d1) /\ (Q <<->> post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost      => 
      (* post d is the loop invariant and the initial precondition *)
      (P ->> post d)  
      /\ (Pbody <<->> (fun st => post d st /\ bassn b st))
      /\ (Ppost <<->> (fun st => post d st /\ ~(bassn b st)))
      /\ verification_conditions Pbody d
  | DCPre P' d         => 
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q        => 
      verification_conditions P d /\ (post d ->> Q)
  end.

(** And now, the key theorem, which captures the claim that the
    [verification_conditions] function does its job correctly.  Not
    surprisingly, we need all of the Hoare Logic rules in the
    proof. *)
(** We have used _in_ variants of several tactics before to
    apply them to values in the context rather than the goal. An
    extension of this idea is the syntax [tactic in *], which applies
    [tactic] in the goal and every hypothesis in the context.  We most
    commonly use this facility in conjunction with the [simpl] tactic,
    as below. *)

Theorem verification_correct : forall d P, 
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq". 
    inversion H as [H1 H2]. clear H. 
    eapply hoare_seq. 
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn". 
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [[Hd11 Hd12] 
                                  [[Hd21 Hd22] [HThen HElse]]]]].
    clear H.
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      eapply hoare_consequence_pre; eauto.
      eapply hoare_consequence_post; eauto.
      eapply hoare_consequence_pre; eauto.
      eapply hoare_consequence_post; eauto.
  Case "While".
    inversion H as [Hpre [[Hbody1 Hbody2] [[Hpost1 Hpost2]  Hd]]];
    subst; clear H.
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  Case "Pre".
    inversion H as [HP Hd]; clear H. 
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(** ** Examples *)

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions (fun st => True) dec_while).
(**
==>
(((fun _ : state => True) ->> (fun _ : state => True)) /\
 ((fun _ : state => True) ->> (fun _ : state => True)) /\
 (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) =
 (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) /\
 (fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) =
 (fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) /\
 (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) ->>
 (fun _ : state => True) [X |-> AMinus (AId X) (ANum 1)]) /\
(fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) ->>
(fun st : state => st X = 0) 
*)

(** In principle, we could certainly work with them using just the
    tactics we have so far, but we can make things much smoother with
    a bit of automation.  We first define a custom [verify] tactic
    that applies splitting repeatedly to turn all the conjunctions
    into separate subgoals and then uses [omega] and [eauto] (a handy
    general-purpose automation tactic that we'll discuss in detail
    later) to deal with as many of them as possible. *)

Lemma ble_nat_true_iff : forall n m : nat,
  ble_nat n m = true <-> n <= m.
Proof.
  intros n m. split. apply ble_nat_true.
  generalize dependent m. induction n; intros m H. reflexivity.
    simpl. destruct m. inversion H.
    apply le_S_n in H. apply IHn. assumption.
Qed.

Lemma ble_nat_false_iff : forall n m : nat,
  ble_nat n m = false <-> ~(n <= m).
Proof.
  intros n m. split. apply ble_nat_false.
  generalize dependent m. induction n; intros m H.
    apply ex_falso_quodlibet. apply H. apply le_0_n.
    simpl. destruct m. reflexivity.
    apply IHn. intro Hc. apply H. apply le_n_S. assumption.
Qed.

Tactic Notation "verify" :=
  apply verification_correct; 
  repeat split;
  simpl; unfold assert_implies; 
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite update_eq;
  repeat (rewrite update_neq; [| reflexivity]);
  simpl in *; 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  repeat rewrite ble_nat_true_iff in *;
  repeat rewrite ble_nat_false_iff in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples [verify] immediately solves the goal (provided
    that the annotations are correct). *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
    {{ fun st => st X = x /\ st Z = z }} ->>
    {{ fun st => st Z - st X = z - x }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => st Z - st X = z - x /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = z - x }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => st Z - (st X - 1) = z - x }} ;
     X ::= AMinus (AId X) (ANum 1) 
       {{ fun st => st Z - st X = z - x }}
  END
    {{ fun st => st Z - st X = z - x /\ st X = 0 }} ->>
    {{ fun st => st Z = z - x }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall x z, 
  dec_correct (subtract_slowly_dec x z).
Proof. intros x z. verify. (* this grinds for a bit! *) Qed.

(** **** Exercise: 3 stars, optional (slow_assignment_dec) *)

(** A roundabout way of assigning a number currently stored in [X] to
   the variable [Y] is to start [Y] at [0], then decrement [X] until it
   hits [0], incrementing [Y] at each step.

   Here is an informal decorated program that implements this idea
   given a parameter [x]: 
      {{ X = x }}
    Y ::= 0;
      {{ X = x /\ Y = 0 }} ->>
      {{ Y + X = x }}
    WHILE X <> 0 DO
        {{ Y + X = x /\ X <> 0 }} ->>
        {{ Y + (X - 1) + 1 = x }}
      X ::= X - 1;
        {{ Y + X + 1 = x }}
      Y ::= Y + 1;
        {{ Y + X = x }}
    END
      {{ Y + X = x /\ X = 0 }} ->>
      {{ Y = x }}
*)

(** Write a corresponding formal decorated program (parametrized by [x])
    and prove it correct. *)

Example slow_assignment_dec (x:nat) : dcom :=
(* FILL IN HERE *) admit.

Theorem slow_assignment_dec_correct : forall x,
  dec_correct (slow_assignment_dec x).
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (factorial_dec)  *)
(** Remember the factorial function we worked with before: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Following the pattern of [subtract_slowly_dec], write a decorated
    Imp program that implements the factorial function, and prove it
    correct. *)

(* FILL IN HERE *)
(** [] *)


(* $Date: 2013-03-11 14:56:33 -0400 (Mon, 11 Mar 2013) $ *)

