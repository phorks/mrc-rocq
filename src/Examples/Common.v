From Stdlib Require Import Strings.String.
From MRC Require Import RefCalc.

Definition x := Model.raw_var "x".
Definition y := Model.raw_var "y".
Definition z := Model.raw_var "z".
Definition t := Model.raw_var "t".
Definition i := Model.raw_var "i".
Definition j := Model.raw_var "j".
Definition k := Model.raw_var "k".

Definition x₀ := Model.to_initial_var x.
Definition y₀ := Model.to_initial_var y.
Definition z₀ := Model.to_initial_var z.
Definition t₀ := Model.to_initial_var t.
Definition i₀ := Model.to_initial_var i.
Definition j₀ := Model.to_initial_var j.
Definition k₀ := Model.to_initial_var k.
