ataca: A TACtic library for Agda
================================

This library provides an interface for writing tactics for Agda. It
also provides several basic tactics and tactic combinators.

Currently the following tactics are supported:

* exact: solve a goal with an explicitly given value
* admit: solve a goal by creating a new postulate
* assumption: search the context for a variable that fits the goal
* intro: refine the goal by introducing a lambda
* intros: refine the goal by introducing as many lambdas as possible
* introAbsurd: solve the goal with an absurd lambda
* introConstructor: refine the goal by introducing a constructor that fits the hole
* introConstructors: refine the goal by repeatedly introducing constructors that fit the (sub)goals
* refine: refine the goal with a given term applied to some arguments
* mini-auto: repeatedly apply assumption, intro, and introConstructor
* mini-auto-with: repeatedly apply assumption, intro, introConstructor, and refine with terms from a given list of hints
* destruct: case split on the given variable (using a pattern-matching lambda)

The library is currently still work in progress and anything is
subject to change at any time.