import «Arith».AST

open Expr
open OpN
--open Op0
open Op1
open Op2

def exampl : Expr := letstd ["x","y"] [integer 1,integer 2] (var "x")
