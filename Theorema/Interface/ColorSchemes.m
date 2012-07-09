
(* Usage of colors:
	0 -> Notebook background
	1 -> Logo foreground
	2 -> Logo background
	3 -> Logo Theorema
	4 -> Logo text
	5 -> Placeholder BG
	6 -> 
	7 -> GUI Tab names
	8 -> Placeholder frame
	9 -> GUI Formula uneval, SelectionPlaceholder BG
	10 ->
	11 -> SelectionPlaceholder FG
	12 -> GUI Formula eval
	13 ->
	14 ->
	15 ->
	
	Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i], {i,0,15}]
*)

(* HOWTO: 

	1) After adding a new color scheme, run `admin`makeColorScheme[newName] in order to generate the necessary stylesheets.
	2) After modifying one of the template stylesheets, run `admin`makeColorScheme[] in order to re-generate all stylesheets. *)

`admin`makeColorScheme[ ] := `admin`makeColorScheme[ $availableColorSchemes]
`admin`makeColorScheme[ names_List] := Scan[ `admin`makeColorScheme, names]
`admin`makeColorScheme[ name_String] :=
	Module[{styles, file},
		styles = NotebookGet[ NotebookOpen[ 
			FileNameJoin[ {$TheoremaDirectory, "Theorema", "FrontEnd", "StyleSheets", "Theorema", "GUIColors-Template.nb"}],
			Visible -> False]];
		file = FileNameJoin[ {$TheoremaDirectory, "Theorema", "FrontEnd", "StyleSheets", "Theorema", "GUI-"<>name<>".nb"}];
		If[ FileExistsQ[ file], DeleteFile[ file]];
		Print[ file];
		Put[ styles /. Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i, name], {i, 0, 15}], file];
	]
`admin`makeColorScheme[ args___] := unexpected[ `admin`makeColorScheme, {args}]
	

TMAcolor[ n_Integer] := TMAcolor[ n, $TheoremaColorScheme]
TMAcolorScheme[ name_String, opts___] := Graphics[ Raster[ Partition[ Apply[ List, Array[ TMAcolor[ #, name]&, 16, 0], {1}], 4]], opts]

(*
  Color Scheme "Milano" derived from fashion collection of Rosso35, Milano
*) 
TMAcolor[ 0, "Milano"] = RGBColor[ 0.91, 0.90, 0.85]; (* beige *)
TMAcolor[ 1, "Milano"] = RGBColor[0.29, 0.46, 0.60]; (* strong blue *)
TMAcolor[ 2, "Milano"] = RGBColor[0.36, 0.54, 0.69]; (* light blue grey *)
TMAcolor[ 3, "Milano"] = RGBColor[ 0.84, 0.70, 0.55]; (* gold *)
TMAcolor[ 4, "Milano"] = RGBColor[ 0.88, 0.88, 0.92]; (* grey90 *)
TMAcolor[ 5, "Milano"] = RGBColor[ 0.73, 0.74, 0.84]; (* grey75 *)
TMAcolor[ 6, "Milano"] = RGBColor[ 0.10, 0.44, 0.41]; (* green *)
TMAcolor[ 7, "Milano"] = RGBColor[ 0.72, 0.35, 0.48]; (* red *)
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