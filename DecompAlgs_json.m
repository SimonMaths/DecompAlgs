/*

Functions for loading and saving a DecAlg as a json object

*/
import "DecAlg.m": library_location;


/*

Serialise a decomposition algebra

*/
intrinsic SaveDecompositionAlgebra(A::DecAlg, filename::MonStgElt)
  {
  Saves a decomposition algebra in JSON format.
  }
  vprintf DecAlg, 2: "Saving decomposition algebra...";
  
  // We check to see if the path exists and if not create it.
  paths := Split(filename, "/");
  path := &cat[ p cat "/" : p in paths[1..#paths-1]];
  System(Sprintf("mkdir -p '%o'", path));
  
  // Check filename
  fname := paths[#paths];
  if "." in fname then
    fsplit := Split(fname, ".");
    assert #fsplit eq 2;
    require fsplit[2] eq "json": "The filename should have the json extension (this will be added if left out)";
  else
    filename := filename cat ".json";
  end if;
  
  // To save larger algebras without hitting magma's limit on strings of 2^31 bits we do each element in the list seperately
  L := [ J[2..#J-2] where J := JSON([*l*]) : l in DecAlgToList(A) ];
  
  System(Sprintf("rm -fr '%o'", filename));
  maxlength := 8000;
  str := "{\n" cat L[1];
  for l in L[2..#L] do
    // we remove some stray "\n"
    ll := l[1] eq "\n" select (l[#l] eq "\n" select l[2..#l-1] else l[2..#l])
             else l[#l] eq "\n" select l[1..#l-1] else l;
    if #str + #ll lt maxlength then
      str cat:= ",\n" cat ll;
    else
      PrintFile(filename, str cat ",");
      str := ll;
    end if;
  end for;
  PrintFile(filename, str cat "\n}");
  
  vprintf DecAlg, 2: " complete!\n";
end intrinsic;

intrinsic DecAlgToList(A::DecAlg) -> List
  {
  Converts a decomposition algebra, axial decompositon algebra, or axial algebra to a list prior to serialising as a JSON object.
  }
  alg := [* *];
  if Type(A) eq DecAlg then
    class := "Decomposition algebra";
  elif Type(A) eq AxlDecAlg then
    class := "Axial decomposition algebra";
  elif Type(A) eq AxlAlg then
    class := "Axial algebra";
  end if;
  Append(~alg, <"class", class>);

  Append(~alg, <"ring", Sprintf("%m", BaseRing(A))>);
  Append(~alg, <"fusion law", FusLawToList(FusionLaw(A))>);
  
  Append(~alg, <"multiplication", Multiplication(A)>);
  
  if assigned A`Miyamoto_group and IsMiyamotoClosed(A) then
    Append(~alg, <"IsMiyamotoClosed", true>);
    // We will only store orbit representatives of the decompositions
    G := MiyamotoGroup(A);
    keys := {@ t[2] : t in OrbitRepresentatives(G) @};
    Ds := {@ Decompositions(A)[i] : i in keys @};
  else
    Append(~alg, <"IsMiyamotoClosed", false>);
    Ds := Decompositions(A);
    keys := IndexSet(A);
  end if;
  
  FL := FusionLaw(A);
  decomps := AssociativeArray();
  for i in [1..#keys] do
    D := Ds[i];
    decomp := AssociativeArray();
    // Need to run over the elements in the set, rather than FusLawElts so they can be JSONised
    decomp["parts"] := [* [* x, Part(D, FL!x) *] : x in FL`set *];
    if IsAxial(D) then
      decomp["axis"] := Eltseq(Axis(D));
    end if;
    decomps[keys[i]] := decomp;  
  end for;
  Append(~alg, <"decompositions", decomps>);
  
  if assigned A`Miyamoto_group then
    assert assigned A`Miyamoto_map;
    
    gen := GeneratorsSequence(MiyamotoGroup(A));
    Append(~alg, <"Miyamoto action", [* [*gen[i], MiyamotoAction(A, gen[i]) *] : i in [1..#gen] *]>);
  end if;
  
  if assigned A`universal_Miyamoto_group then
    assert assigned A`universal_projection and assigned A`Miyamoto_group;
    
    UMiy, phi := UniversalMiyamotoGroup(A);
    gen := GeneratorsSequence(UMiy);
    Append(~alg, <"universal Miyamoto projection", [* [*gen[i], gen[i]@phi *] : i in [1..#gen] *]>);
  end if;
  
  if ISA(Type(A), AxlAlg) and assigned A`Frobenius_form then
    Append(~alg, <"Frobenius form", FrobeniusForm(A)>);
  end if;
  
  return alg;
end intrinsic;
//
// =============== Code to load a DecAlg ================
//
intrinsic LoadDecompositionAlgebra(filename::MonStgElt) -> .
  {
  Loads a decomposition algebra from the location given.
  }
  vprintf DecAlg, 2: "Loading decomposition algebra...";
  paths := Split(filename, "/");
  if "." notin paths[#paths] then
    realfilename := filename cat ".json";
  else
    realfilename := filename;
  end if;
  
  string := Read(realfilename);
  // remove any end of line characters that magma tends to add
  string := &cat Split(string, "\\\n");
  alg := ParseJSON(string);
  vprintf DecAlg, 2: " complete!\n";
  return DecompositionAlgebra(alg);
end intrinsic;

intrinsic DecompositionAlgebra(alg::Assoc) -> DecAlg
  {
  Creates a decomposition algebra, axial decomposition algebra, or axial algebra from an associative array.  We assume that the associative array represents the algebra stored in json format.
  }
  keys := Keys(alg);
  require "class" in keys: "The file given does correspond to a json - no class";
  
  if alg["class"] eq "Decomposition algebra" then
    A := New(DecAlg);
  elif alg["class"] eq "Axial decomposition algebra" then
    A := New(AxlDecAlg);
  elif alg["class"] eq"Axial algebra" then
    A := New(AxlAlg);
  else
    error "The file given does not encode a decomposition algebra.";
  end if;
  
  A`fusion_law := FusionLaw(alg["fusion law"]);
  
  R := eval(alg["ring"]);
  mult := Matrix(R, alg["multiplication"]);
  A`algebra := Algebra< R, Ncols(mult) | Rows(mult)>;
  
  if "Miyamoto action" in keys then
    gens := [Numbers(k[1]) : k in alg["Miyamoto action"]];
    images := [Matrix(R, k[2]) : k in alg["Miyamoto action"]];
    G := PermutationGroup< #gens[1] | gens>;
    A`Miyamoto_group := G;
    
    matG := MatrixGroup<Dimension(A), R | images>;
    A`Miyamoto_map := hom<G -> matG | [<G!gens[i], matG!images[i]> : i in [1..#gens]]>;
  end if;
  
  decs := alg["decompositions"];
  V := VectorSpace(A);
  Ds := [**];
  
  for k in Keys(decs) do
    partkeys := {@ t[1] : t in decs[k]["parts"] @};
    assert forall{ i : i in partkeys | IsCoercible(FusionLaw(A), i)} and #partkeys eq #FusionLaw(A);
    
    S := [ RSpace(t[2]) : t in decs[k]["parts"] ];
    
    if "axis" in Keys(decs[k]) then
      axis := Numbers(decs[k]["axis"]);
      D := AxialDecomposition(A, S, axis);
    else
      D := Decomposition(A, S);
    end if;
    
    kk := eval(k); // This is normally a RngIntElt, but could be something else
    Append(~Ds, <kk, D>);
  end for;
  
  if alg["IsMiyamotoClosed"] then
    // Assume if it is Miyamoto closed, the permutation group G has the natural action on the keys of the decompositions.
    G := MiyamotoGroup(A);
    Ax := GSet(G);
    orbits := Orbits(G);
    assert #Ds eq #orbits and forall{t : t in Ds | exists{o : o in orbits | t[1] in o}};
    
    for t in Ds do
      i, D := Explode(t);
      // Get the orbit corresponding to t
      assert exists(o){o : o in orbits | i in o};
      
      for j in o diff {i} do
        so, g := IsConjugate(G, i, j);
        assert so;
        
        Append(~Ds, <j,D*g>);
      end for;
    end for;
  end if;
  A`decompositions := AssociativeArray(Ds);

  if "universal Miyamoto projection" in keys then
    gens := [Numbers(k[1]) : k in alg["universal Miyamoto projection"]];
    images := [Numbers(k[2]) : k in alg["universal Miyamoto projection"]];
    
    UMiy := PermutationGroup< #gens[1] | gens>;
    A`universal_Miyamoto_group := UMiy;
    
    G := PermutationGroup< #images[1] | images>;
    assert G eq MiyamotoGroup(A);
    
    A`universal_projection := hom<UMiy -> G | [<UMiy!gens[i], G!images[i]> : i in [1..#gens]]>;
  end if;
  
  if ISA(Type(A), AxlAlg) and "Frobenius form" in keys then
    A`Frobenius_form := Matrix(R, alg["Frobenius form"]);
  end if;

  return A;
end intrinsic;
