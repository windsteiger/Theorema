
(* Usage of colors:
	0 -> Logo Theorema, GUI BG, main GUI pane BG
	1 -> Logo foreground, GUI button bar BG (GUI frame)
	2 -> Logo background
	3 -> Notebook background
	4 -> Archive info BG
	5 -> Placeholder BG, div. notebook cell brackets, Archive header BG
	6 -> Info cells label FG
	7 -> GUI labels FG, notebook computation marker
	8 -> Logo text, Placeholder frame, notebook env header BG
	9 -> GUI Formula uneval, SelectionPlaceholder BG, Global decl. marker
	10 -> notebook frame labels
	11 -> SelectionPlaceholder FG, Notebook (Sub(Sub))Title FG, notebook computation FG, Info cells content FG, Button text
	12 -> GUI Formula eval, notebook env formula FG
	13 ->
	14 -> Notebook SubSub(Sub(Sub))Section FG, notebook env delimiters borderline
	15 -> Notebook (Sub)Section FG
	
	Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i], {i,0,15}]
*)

TMAcolor[ n_Integer] := TMAcolor[ n, $TheoremaColorScheme]
TMAcolorScheme[ name_String, opts___] := Graphics[ Raster[ Partition[ Apply[ List, Array[ TMAcolor[ #, name]&, 16, 0], {1}], 4]], opts]

(*
  Color Scheme "Milano" derived from fashion collection of Rosso35, Milano
*) 
TMAcolor[ 0, "Milano"] = RGBColor[ 0.91, 0.90, 0.85]; (* beige *)
TMAcolor[ 1, "Milano"] = RGBColor[0.29, 0.46, 0.60]; (* strong blue *)
TMAcolor[ 2, "Milano"] = RGBColor[0.36, 0.54, 0.69]; (* light blue grey *)
TMAcolor[ 3, "Milano"] = RGBColor[0.957, 0.96, 0.97]; (* grey96 *)
TMAcolor[ 4, "Milano"] = RGBColor[ 0.88, 0.88, 0.92]; (* grey90 *)
TMAcolor[ 5, "Milano"] = RGBColor[ 0.73, 0.74, 0.84]; (* grey75 *)
TMAcolor[ 6, "Milano"] = RGBColor[0.404, 0.43, 0.545]; (* blue *)
TMAcolor[ 7, "Milano"] = RGBColor[0.486, 0.33, 0.32]; (* brown *)
TMAcolor[ 8, "Milano"] = RGBColor[ 0.89, 0.80, 0.69]; (* light brown *)
TMAcolor[ 9, "Milano"] = RGBColor[ 0.73, 0.65, 0.61]; (* medium brown *)
TMAcolor[ 10, "Milano"] = RGBColor[ 0.55, 0.44, 0.42]; (* choko *)
TMAcolor[ 11, "Milano"] = RGBColor[ 0.23, 0.25, 0.34]; (* blue grey *)
TMAcolor[ 12, "Milano"] = RGBColor[ 0.25, 0.19, 0.20]; (* dark brown *)
TMAcolor[ 13, "Milano"] = RGBColor[ 0.55, 0.55, 0.55]; (* grey55 *)
TMAcolor[ 14, "Milano"] = RGBColor[ 0.40, 0.40, 0.40]; (* grey40*)
TMAcolor[ 15, "Milano"] = RGBColor[ 0.30, 0.30, 0.30]; (* grey30 *)

(*
  Color Scheme "Genova" derived from Mathematica ColorData[46], use ColorData["Indexed", "Image"]
*)
TMAcolor[ 0, "Genova"] = ColorData[46][10];
TMAcolor[ 1, "Genova"] = ColorData[46][1];
TMAcolor[ 2, "Genova"] = ColorData[46][4];
TMAcolor[ 3, "Genova"] = ColorData[46][15];
TMAcolor[ 4, "Genova"] = ColorData[46][7];
TMAcolor[ 5, "Genova"] = ColorData[46][7];
TMAcolor[ 6, "Genova"] = ColorData[46][7];
TMAcolor[ 7, "Genova"] = ColorData[46][7];
TMAcolor[ 8, "Genova"] = ColorData[46][7];
TMAcolor[ 9, "Genova"] = ColorData[46][7];
TMAcolor[ 10, "Genova"] = ColorData[46][7];
TMAcolor[ 11, "Genova"] = ColorData[46][7];
TMAcolor[ 12, "Genova"] = ColorData[46][7];
TMAcolor[ 13, "Genova"] = ColorData[46][7];
TMAcolor[ 14, "Genova"] = ColorData[46][7];
TMAcolor[ 15, "Genova"] = ColorData[46][7];

(*
  Color Scheme "Torino" derived from Mathematica ColorData[36/38], use ColorData["Indexed", "Image"]
*)
TMAcolor[ 0, "Torino"] = ColorData[36][1];
TMAcolor[ 1, "Torino"] = ColorData[36][7];
TMAcolor[ 2, "Torino"] = ColorData[36][8];
TMAcolor[ 3, "Torino"] = ColorData[38][1];
TMAcolor[ 4, "Torino"] = ColorData[36][1];
TMAcolor[ 5, "Torino"] = ColorData[36][7];
TMAcolor[ 6, "Torino"] = ColorData[36][7];
TMAcolor[ 7, "Torino"] = ColorData[36][7];
TMAcolor[ 8, "Torino"] = ColorData[36][7];
TMAcolor[ 9, "Torino"] = ColorData[36][7];
TMAcolor[ 10, "Torino"] = ColorData[36][7];
TMAcolor[ 11, "Torino"] = ColorData[36][7];
TMAcolor[ 12, "Torino"] = ColorData[36][7];
TMAcolor[ 13, "Torino"] = ColorData[36][7];
TMAcolor[ 14, "Torino"] = ColorData[36][7];
TMAcolor[ 15, "Torino"] = ColorData[36][7];

(* Global variables *)

$availableColorSchemes = Union[ Cases[ DownValues[TMAcolor], TMAcolor[ _Integer, name_String] -> name, {3}]];
$TheoremaColorScheme = "Milano";