module Reflection where

import Tactic.Reflection
module TC = Tactic.Reflection
open TC using
  ( Name ; Term ; Type ; Arg ; ArgInfo ; unArg ; getArgInfo
  ; Abs ; unAbs
  ; Visibility ; getVisibility
  ; Relevance ; getRelevance
  ; Telescope
  ; Pattern ; Clause ; Definition
  ; TC ; ErrorPart
  ) public
open Term       public
open Arg        public
open Abs        public
open ArgInfo    public
open Visibility public
open Relevance  public
open Pattern    public
open Clause     public
open Definition public
open ErrorPart  public
