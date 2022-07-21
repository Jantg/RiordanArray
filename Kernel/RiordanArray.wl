(* ::Package:: *)

BeginPackage["RiordanArray`"]

(* Declare your package's public symbols here. *)

RiordanArray::usage = "The main object of this package"
RiordanArrayGeneratingFunctions::usage = "It extracts (g(t),f(t)) from the RiordanArray object"
RiordanArrayColumnGeneratingFunction::usage = "It extracts g(t)f(t\!\(\*SuperscriptBox[\()\), \(k\)]\) from the RiordanArray object"
FTRA::usage = "It applies the Fundamental Theorem of Riordan Array"
ASequence::usage = "It finds the A-sequence of the given RiordanArray object"
ZSequence::usage = "It finds the Z-sequence of the given RiordanArray object"
RiordanArrayFromAZSequences::usage = "Given A/Z-sequences and initial value, return the correspondingRiordanArray[] object"
Begin["`Private`"]

(* Define your public and private symbols here. *)

(* 
Note: g(t)= Subscript[g, 0]+Subscript[g, 1]t+\[CenterEllipsis] must have a nonzero Subscript[g, 0] while f(t)= Subscript[f, 0]+Subscript[f, 1]t+\[CenterEllipsis] must have Subscript[f, 0]=0 and nonzero Subscript[f, 1].
However, due to complicated arithmetic we do with RiordanArray[], sometimes g(t) and f(t) while 
meeting these constraints do not appear as they do unless Simplify[] is used accordingly. Hence, 
the condition /;g[0]*f'[0]!= 0 is not imposed explicitly here
*)

RiordanArray[g_,f_][n_Integer?NonNegative,k_Integer?NonNegative]:=SeriesCoefficient[g[t]*Power[f[t],k],{t,0,n}];

(*RiordanArray[g_,f_][n_Integer?NonNegative,k_Integer?NonNegative][assoc_]:=SeriesCoefficient[(g[t]/.assoc)*Power[(f[t]/.assoc),k],{t,0,n}];*)

(*
Extract the kStart column to the kEnd column of the n-th row. All elements after the n-th column 
should be zero because the RA is lower-triangular.
*)
RiordanArray[g_, f_][n_Integer?NonNegative, kStart_Integer?NonNegative ;; kEnd_Integer?NonNegative] /; kEnd >= kStart :=
 If[kStart > n, ConstantArray[0, kEnd - kStart + 1], 
 If[kEnd > n, Join[(SeriesCoefficient[g[t]*Power[f[t], #], {t, 0, n}]) & /@ Range[kStart, n], 
 ConstantArray[0, kEnd - n]], (SeriesCoefficient[g[t]*Power[f[t], #], {t, 0, n}]) & /@ Range[kStart, kEnd]]];
 
(*RiordanArray[g_, f_][n_Integer?NonNegative, kStart_Integer?NonNegative ;; kEnd_Integer?NonNegative][assoc_]/; kEnd >= kStart :=
 If[kStart > n, ConstantArray[0, kEnd - kStart + 1], 
 If[kEnd > n, Join[(SeriesCoefficient[(g[t]/.assoc)*Power[(f[t]/.assoc), #], {t, 0, n}]) & /@ Range[kStart, n], 
 ConstantArray[0, kEnd - n]], (SeriesCoefficient[(g[t]/.assoc)*Power[(f[t]/.assoc), #], {t, 0, n}]) & /@ Range[kStart, kEnd]]];*)
 
(*
Extract the nStart row to the nEnd row of the k-th column. This amounts to obtaining the coefficients
of t^nStart to t^nEnd for the column generating function g(t)f(t)^k
*)
RiordanArray[g_,f_][nStart_Integer?NonNegative;;nEnd_Integer?NonNegative,k_Integer?NonNegative]/;nEnd>=nStart:=
CoefficientList[Series[g[t]*Power[f[t],k],{t,0,nEnd}],t][[(nStart+1);;(nEnd+1)]];

(*RiordanArray[g_,f_][nStart_Integer?NonNegative;;nEnd_Integer?NonNegative,k_Integer?NonNegative][assoc_]/;nEnd>=nStart:=
CoefficientList[Series[(g[t]/.assoc)*Power[(f[t]/.assoc),k],{t,0,nEnd}],t][[(nStart+1);;(nEnd+1)]];*)

(*
Combination of the above two cases, extract the submatrix of the Riordan array
*)
RiordanArray[g_,f_][nStart_Integer?NonNegative;;nEnd_Integer?NonNegative,kStart_Integer?NonNegative;;kEnd_Integer?NonNegative]/;nEnd>=nStart&&kEnd>=kStart:=
CoefficientList[Series[g[t]*Power[f[t],#],{t,0,nEnd}],t,{nEnd+1}][[(nStart+1);;(nEnd+1)]]&/@Range[kStart,kEnd]//Transpose;

(*RiordanArray[g_,f_][nStart_Integer?NonNegative;;nEnd_Integer?NonNegative,kStart_Integer?NonNegative;;kEnd_Integer?NonNegative][assoc_]/;nEnd>=nStart&&kEnd>=kStart:=
CoefficientList[Series[(g[t]/.assoc)*Power[(f[t]/.assoc),#],{t,0,nEnd}],t,{nEnd+1}][[(nStart+1);;(nEnd+1)]]&/@Range[kStart,kEnd]//Transpose;*)


(*MatrixForm with optional argument specifying the range of the RiordanArray object. It will return its visualization with appropriate padding*)

(*nStart ==0, kStart == 0 case*)
RiordanArray/:MatrixForm[RiordanArray[g_,f_],{nStart_Integer?NonNegative;;nEnd_Integer?NonNegative,kStart_Integer?NonNegative;;kEnd_Integer?NonNegative}]/;nEnd>=nStart&&kEnd>=kStart:=
If[nStart == 0 && kStart == 0,
	Join[Map[PadRight[#,(kEnd+2),"\[CenterEllipsis]"]&,RiordanArray[g,f][nStart;;nEnd,kStart;;kEnd],1],List[Join[ConstantArray["\[VerticalEllipsis]",(kEnd+1)],{"\[DescendingEllipsis]"}]]]//MatrixForm,
	If[nStart != 0, 
		If[kStart == 0, Join[List[Join[ConstantArray["\[VerticalEllipsis]",(kEnd+1)],{"\[AscendingEllipsis]"}]],Join[Map[PadRight[#,(kEnd+2),"\[CenterEllipsis]"]&,RiordanArray[g,f][nStart;;nEnd,kStart;;kEnd],1],List[Join[ConstantArray["\[VerticalEllipsis]",(kEnd+1)],{"\[DescendingEllipsis]"}]]]]//MatrixForm,
						Join[List[Join[{"\[DescendingEllipsis]"},ConstantArray["\[VerticalEllipsis]",(kEnd+1-kStart)],{"\[AscendingEllipsis]"}]],Join[Map[PadLeft[PadRight[#,(kEnd+2-kStart),"\[CenterEllipsis]"],(kEnd+3-kStart),"\[CenterEllipsis]"]&,RiordanArray[g,f][nStart;;nEnd,kStart;;kEnd],1],List[Join[{"\[AscendingEllipsis]"},ConstantArray["\[VerticalEllipsis]",(kEnd+1-kStart)],{"\[DescendingEllipsis]"}]]]]//MatrixForm],
		Join[Map[PadLeft[PadRight[#,(kEnd+2-kStart),"\[CenterEllipsis]"],(kEnd+3-kStart),"\[CenterEllipsis]"]&,RiordanArray[g,f][nStart;;nEnd,kStart;;kEnd],1],List[Join[{"\[AscendingEllipsis]"},ConstantArray["\[VerticalEllipsis]",(kEnd+1-kStart)],{"\[DescendingEllipsis]"}]]]//MatrixForm]
]



(* RiordanArrayGeneratingFunctions returns g(t) and f(t) of the RiordanArray object*)

(* Default with only the RiordanArray[] as an argument returns a pure function*)
RiordanArrayGeneratingFunctions[RiordanArray[g_,f_]]:={g[#]&,f[#]&};

(* 
With an optional argument {t,n}, it returns them as a Series object with a 
variable t explicitly evaluated up to its n-th order term t^n and the rest as O[t]^(n+1)
*)
RiordanArrayGeneratingFunction[RiordanArray[g_,f_],{t_,n_Integer?NonNegative}]:=
{Series[g[t],{t,0,n}],Series[f[t],{t,0,n}]};


(* RiordanArrayColumnGeneratingFunction returns g(t)f(t)^k of the RiordanArray object once k is given*)

(* Default with RiordanArray[] and k as arguments returns a pure function*)
RiordanArrayColumnGeneratingFunction[RiordanArray[g_,f_],k_]:=
(g[#]*Power[f[#],k])&

(* 
With an optional argument {t,n}, it returns them as a Series object with a 
variable t explicitly evaluated up to its n-th order term t^n and the rest as O[t]^n+1
*)
RiordanArrayColumnGeneratingFunction[RiordanArray[g_,f_],k_Integer?NonNegative,{t_,n_Integer?NonNegative}]:=
Series[(g[t]*Power[f[t],k]),{t,0,n}]



(* Create a fancy icon for the RiordanArray object*)

(* 
In future work, RiordanArray object should encompass generalized Riordan array
and Riordan arrays that are not proper too. Relevant features of those will likely
be defined in the empty list {} next to the StandardForm where additional features
of the RiordanArray icon can be given.
*)
RiordanArray/:MakeBoxes[ra:RiordanArray[g_,f_],StandardForm]:= 
BoxForm`ArrangeSummaryBox[RiordanArray,ra, ArrayPlot[RiordanArray[g,f][0;;4,0;;4],
ColorFunction->"Rainbow",ColorFunctionScaling->True],
{{"g(t) =",g["t"]},{"f(t) =",f["t"]}},{},StandardForm]


(* Rules for multiplication which is a very fundamental operation on Riordan Arrays *)

(*Dot product of two Rirodan arrays is yet another Riordan array *)
RiordanArray/:RiordanArray[g1_,f1_] . RiordanArray[g2_,f2_]:=RiordanArray[g1[#]*g2[f1[#]]&,f2[f1[#]]&]

(* 
Riordan Array multiplied by an infinite dimensional column vector whose k-th row Subscript[h, k] is 
a k-th coefficient of a generating function h(t)= Subscript[h, 0]+Subscript[h, 1]t+\[CenterEllipsis]+Subscript[h, k]t^k+\[CenterEllipsis] is an infinite dimensional
column vector following a generating function g(t)h(f(t)). This is the Fundamental Theorem 
of Riordan Arrays (FTRA) extremely useful for combinatorial enumeration.
*)
FTRA[RiordanArray[g_,f_],h_,k_]:=
RiordanArrayColumnGeneratingFunction[RiordanArray[g,f] . RiordanArray[(GeneratingFunction[h[#],k,#])&,(1)&],0]


(* Inverse of a Riordan array is also another Riordan array*)

RiordanArray/:Inverse[RiordanArray[g_,f_]]:=With[{finv=InverseFunction[f]},RiordanArray[Power[g[finv[#]],-1]&,finv[#]&]]


(* Alternative characterization of the Riordan array using A,Z-sequences and the initial value*)

(* 
Coefficient of the A-sequence A(t)=Subscript[a, 0]+Subscript[a, 1]t + Subscript[a, 2]t^2+\[CenterEllipsis] fully describes the linear relationship 
between any (n+1,k+1)-th cell and (n,k)-th,(n,k+1)-th, ... (n,n)-th cells for all n,k\[Element]Subscript[\[DoubleStruckCapitalN], 0]
*)
ASequence[RiordanArray[g_,f_]]:=With[{finv=InverseFunction[f]},(#/finv[#])&]

(* 
Coefficient of the Z-sequence A(t)=Subscript[z, 0]+Subscript[z, 1]t + Subscript[z, 2]t^2+\[CenterEllipsis] fully describes the linear relationship 
between any (n+1,0)-th cell and (n,0)-th,(n,1)-th, ... (n,n)-th cells for all n\[Element]Subscript[\[DoubleStruckCapitalN], 0]
*)
ZSequence[RiordanArray[g_,f_]]:=With[{zseq = (Values[First@Solve[{z[u]==(g[t]-SeriesCoefficient[g[t],{t,0,0}])/(t*g[t]),u==f[t]},z[u],{t}]]/.u->#)[[1]]},zseq&]



(*Get usual characterization of the Riordan array given the alternative one based on A/Z sequences and init*)

(* 
With given A and Z sequences (plus the starting value at the (0,0)-th cell), return the 
RiordanArray[] with the corresponding g(t) and f(t).
*)

RiordanArrayFromAZSequences[ASequence_,ZSequence_,dinit_]:=
With[{sols = Solve[Join[{(h[t]/t)==ASequence[h[t]],t>0},(#>0)&/@CoefficientList[ASequence[t],t]],h[t],Reals]},
	With[{f=(Values[First@sols][[1]]/.t->#)&},
		g =(Values[First@Solve[Join[{d[t]== dinit*Power[1-t*ZSequence[f[t]],-1],t>0},(#>0)&/@CoefficientList[ZSequence[t],t]],d[t],Reals]][[1]]/.t->#)&;
		RiordanArray[g,f]
		]
]


End[] (* End `Private` *)

EndPackage[]
