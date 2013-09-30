(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

open Cil
open Pretty

module H = Hashtbl
module E = Errormsg

module MU = Markutil

module N = Ptrnode

let debugVararg = false

(* Assume all non-annotated vararg functions behave like printf. *) 
let assumePrintf = ref false 

(* Autogenerate vararg descriptors *)
let autogenDescriptors = ref true

(* The functions for which we have generated the descriptor automatically *)
let autoDescr: (string, varinfo * compinfo) H.t = H.create 17
(* weimer: Sat Jan 25 14:45:05 PST 2003
 * changed to include the varinfo so that we have the declared location
 * when we print out the warning. Needed for bind. *)

(* Check that s starts with prefix p *)
let prefix p s = 
  let lp = String.length p in
  let ls = String.length s in
  lp <= ls && String.sub s 0 lp = p


let pMarkField = ref (fun _ -> E.s (E.bug "pMarkField not initialized"))

(*********************** VARARG ********************************)

let varargFunctions : (string, typ) H.t = H.create 17
let printfFunctionsByName : (string, int) H.t = H.create 17

(* Once we see the definition of the printf format union we will remember it 
 * here *)
(* NOTE: the order of the fields here determines their numeric codes
 * when passed in __ccured_va_tags, and those codes are hardcoded in
 * CHECK_FORMATARGS in ccuredlib.c *)
(* sm: at one point I thought adding another field for unsigned char*
 * would be a good idea, but that's a little hard; instead, we'll
 * adopt the idea that client code really should be passing char* to
 * "%s" for uniformity of interpretation *)
let printfFormatStruct : typ ref = ref voidType
let getPrintfFormatStruct () = 
  if !printfFormatStruct != voidType then 
    !printfFormatStruct
  else begin
    try
      printfFormatStruct :=
        TComp(fst (H.find MU.allCompinfo "printf_arguments"),[]);
      !printfFormatStruct
    with Not_found -> 
      E.s (E.bug "Cannot find the definition of struct printf_arguments")
  end
  




(* Compute the signature of a type for comparing arguments *)
let argumentTypeSig (t: typ) = 
  let rec argumentPromotion (t : typ) : typ =
    match unrollTypeDeep t with
      (* We assume that an IInt can hold even an IUShort *)
      TInt ((IShort|IUShort|IChar|ISChar|IUChar
             |ILong|IULong|IUInt|IInt), a) -> 
        TInt(IInt, [])
      (* We always drop the unsigned and the attributes on integer *)
    | TInt ((ILongLong|IULongLong), a) -> TInt(ILongLong, [])
          (* floats are passed as double *)
    | TFloat ((FFloat|FDouble), a) -> TFloat (FDouble, [])
    | TEnum (_, a) -> TInt(IInt, [])
    | TPtr(TInt((IChar|IUChar|ISChar), a1), a2) -> TPtr(TInt(IChar, []), [])
    | t -> t
  in
  (* Ignore all attributes *)
  typeSigWithAttrs (fun x -> []) (argumentPromotion t)

type vaKind  = int (* An index starting from 0 *) 
             * string (* A name of the kind *)
             * typ (* The type of the kind *)
             * typsig (* The pre-computed type signature *)


(* Keep track for each function whether it is a vararg, and the 
 * alternatives, with an index, a field name, a type and a type signature. *)
let getVarargKinds (descrt: typ) : vaKind list = 
  let kinds = 
    match unrollType descrt with
      TComp (ci, _) -> 
        let rec loop (idx: int) = function
            [] -> []
          | fi :: restfi -> 
              (idx, fi.fname, fi.ftype, argumentTypeSig fi.ftype) 
              :: loop (idx + 1) restfi
        in
        loop 0 ci.cfields
    | t' -> [(0, "anon", t', argumentTypeSig t')]
  in
  kinds

let docDescr () (descrt: typ) : doc = 
  let kinds = getVarargKinds descrt in
  dprintf "%a: @[%a@]"
    d_type descrt (* union *)
    (docList ~sep:line
       (fun (_,_,tau,_) -> d_type () (setTypeAttrs tau []))) kinds



(* Get the vararg descriptor from some attribute list. If not found then 
 * might try to generate one automatically based on a function varinfo. 
 * Otherwise will make it a printf (if assumePrintf is set) *)
let getVarargDescriptorFromAttributes 
    (a: attributes) 
    ~(tryauto: varinfo option) : typ * bool = 
  match filterAttributes "ccuredvararg" a with 
    Attr(_, [ASizeOf t]) :: _ -> t, false
  | a' -> begin
      match tryauto with 
        Some vi when !autogenDescriptors -> 
          (* Get the auto descriptor type *)
          let _, descrCI = 
            Util.memoize autoDescr vi.vname 
              (fun _ -> (vi,
                mkCompInfo true ("autoVarargDescr_" ^ vi.vname)
                  (fun _ -> []) [])) in
          TComp(descrCI, []), true

      | _ -> (* Now see if we have to assume it is a printf *)
          if !assumePrintf then 
            getPrintfFormatStruct (), false
          else
            raise Not_found
  end

  

let getVarargFunctionDescriptorType (fexp: exp) 
    : typ * bool (* whether it is autogenerated *) = 
  match unrollType (typeOf fexp) with
    TFun(_, _, _, a) as t -> 
      (* See if this is an actual function *)
      let autofun = 
        match fexp with 
          Lval(Var f, NoOffset) -> Some f
        | _ -> None
      in
      getVarargDescriptorFromAttributes a
        ~tryauto:autofun
  
  | _ -> E.s (E.bug "getVarargFunctionDescriptorType on a non-function: %a\n" d_exp fexp)


(* Get the descriptor type for a va_list variable. May raise Not_found *)
let getValistDescriptorType 
    (dv:varinfo) 
    (fvar: varinfo)
    : typ * bool (* whether it is auto *) = 
  match unrollType dv.vtype with 
    TPtr(TComp(ci, _), pa) when prefix "__ccured_va_list" ci.cname ->
      (* See if the markervi has the vararg descriptor *)
      if hasAttribute "ccuredvararg" pa then 
        getVarargDescriptorFromAttributes pa ~tryauto:None
      else begin
        (* It does not. Get the descriptor from the enclosing function *)
        let descrt, isAuto = 
          getVarargFunctionDescriptorType (Lval (var fvar)) in
        descrt, isAuto
      end

  | _ -> 
      E.s (E.bug "getValistDescriptorType not on __ccured_va_list") 
        (* raise Not_found *)
         

(* May raise Not_found *)
let rec findTypeIndex (t: typ) 
                      (descrt: typ)
                      (isAuto: bool)
    : int * string * typ * typsig = 
  let argkinds = getVarargKinds descrt in
  let ts = argumentTypeSig t in
  try
    List.find (fun (_, _, _, ks) -> ks = ts) argkinds
  with Not_found when isAuto -> begin
    (* Add a new field *)
    let ci = match descrt with 
      TComp(ci, _) -> ci
    | _ -> E.s (E.bug "findTypeIndex but not compinfo") 
    in
    let newfld = { fcomp = ci; fname = "auto" ^ (string_of_int (List.length ci.cfields));
                                   ftype = t; fbitfield = None; fattr = [];
                                   floc = locUnknown } 
    in
    !pMarkField newfld;
    (* Add at the end *)
    ci.cfields <- ci.cfields @ [ newfld ];
    (* And try again *)
    try
      findTypeIndex t descrt false (* to prevent recursion *)
    with Not_found -> E.s (E.bug "findTypeIndex loops")
  end

(* Fetch references to the Vararg globals *)
let ccured_va_count_o : lval option ref = ref None
let ccured_va_tags_o : lval option ref = ref None
let ccured_va_count_max = 32
let fetchVarargGlobals () =
  let g1 = 
    match !ccured_va_count_o with 
      Some lv -> lv
    | None -> 
        let g1 = makeGlobalVar "__ccured_va_count" intType in
        g1.vstorage <- Extern;
        g1.vdecl <- !currentLoc;
        MU.theFile := GVarDecl(g1, g1.vdecl) :: !MU.theFile;
        MU.registerGlobalDeclaration g1;
        let g1lval = var g1 in
        ccured_va_count_o := Some g1lval;
        g1lval
  in
  let g2 = 
    match !ccured_va_tags_o with 
      Some lv -> lv
    | None -> 
        let g2 = makeGlobalVar "__ccured_va_tags" 
            (TArray(intType, Some (integer ccured_va_count_max), [])) in
        g2.vstorage <- Extern;
        g2.vdecl <- !currentLoc;
        MU.theFile := GVarDecl(g2, g2.vdecl) :: !MU.theFile;
        MU.registerGlobalDeclaration g2;
        let g2lval = var g2  in
        ccured_va_tags_o := Some g2lval;
        g2lval
  in
  g1, g2


(* take apart a format string and return a list of int/pointer type choices *)
let rec parseFormatString f start = begin
  (* interpret a conversion specifier: the stuff that comes after the % in a 
   * printf format string  *)
  let rec parseConversionSpec f start = begin
    try 
      match Char.lowercase f.[start] with
        'e' | 'f' | 'g' |   (* double arg *)
        'a' ->              (* double arg *)
          [TFloat(FDouble, [])], (start+1)
      | 'd' | 'i' |         (* signed int arg *)
        'o' | 'u' | 'x' |   (* unsigned int arg *)
        'c' |               (* unsigned char *)
        'p' ->              (* void pointer treated as int *)
          [intType], (start+1)
      | '*' ->            (* integer *)
          let a,b = parseConversionSpec f (start+1) in
          intType :: a, b 
      | 's' -> [charPtrType], (start+1) (* char pointer *)
      | 'n' -> E.s (bug "Cannot handle 'n' character in format string [%s]" f)
      | _ -> parseConversionSpec f (start+1)
    with _ ->
      ignore (warn "Malformed format string [%s]" f);
      raise Not_found
  end
  in
  try 
    let i = String.index_from f start '%' in
    if f.[i+1] = '%' then (* an escaped %, not a format char *) 
      parseFormatString f (i+2)
    else begin
      (* look after the % to see if they want an Int or a Pointer *)
      let t, next_start = parseConversionSpec f (i+1) in
      t @ (parseFormatString f next_start) (* look for another % *)
    end
  with _ -> []  (* no more % left in format string *)
end

let createFunc name t: fundec = 
  let fdec = emptyFunction name in
  fdec.svar.vtype <- t;
  (* We also add a prototype. If we don't then cure.ml will not see it *)
  MU.theFile := GVarDecl(fdec.svar, locUnknown) :: !MU.theFile;
  fdec

let checkFormatArgsFun = ref Cil.dummyFunDec
let get_checkFormatArgsFun () : varinfo =
  if !checkFormatArgsFun = dummyFunDec then begin
    checkFormatArgsFun := 
       createFunc "CHECK_FORMATARGS"
         (TFun(intType, 
               Some [ ("format", TPtr(charType, [Attr("rostring",[])]), [])],
               false, []));
  end;
  (!checkFormatArgsFun).svar

let vaInitFun = ref Cil.dummyFunDec
let get_vaInitFun () : varinfo =
  if !vaInitFun = dummyFunDec then begin
    let ccured_va_list, _ = try
      H.find MU.allCompinfo "__ccured_va_list"
    with Not_found ->
      E.s (bug "variable-argument function used, but __ccured_va_list is not defined.  Did you remember to include <stdarg.h>?")
    in
    vaInitFun := 
       createFunc "__ccured_va_init"
         (TFun(voidType, 
               Some [ ("vainfo", TPtr(TComp(ccured_va_list,[]),[]), []) ],
               false, []));
  end;
  (!vaInitFun).svar

(* See if a function has a boxformat argument and return it *)
let getFormatArg (func: exp) 
                 (args: exp list) : exp option = 
  try
    match filterAttributes "ccuredformat" 
        (MU.getFunctionTypeAttributes func) with
      [Attr(_, [AInt format_idx])] -> begin
        let format_arg = 
          try List.nth args (format_idx - 1)
          with _ -> begin
            ignore (warn "Call to format function with too few arguments");
            raise Not_found
          end
        in
        Some format_arg
      end
    | _ -> None
(*
      if (!assumePrintf) then begin
        try 
          Some(List.hd (List.rev args))
        with e -> None
      end else None
*)
  with Not_found -> None
 
(* Special handler for format strings *)
let checkFormatString 
    (format_str: string)
    (descrt: typ) 
    (indices: (int * typ) list) : bool =
  try
    let format_types = parseFormatString format_str 0 in (* May raise 
    * Not_found  *)
    let format_indices = 
      List.map (fun t -> 
        let n, _, _, _ = findTypeIndex t descrt false in n) format_types in
    (* Now commpare the indices. Allow any kind of argument for an 
    * index 0 in the format_indices (corresponds to int) *)
    let intIndex, _, _, _ = 
      try findTypeIndex intType descrt false
      with _ -> E.s (bug "handleFormatString")
    in
    let rec compare indices formats = 
      match indices, formats with
        [], [] -> ()
      | (i, _) :: indices, f :: formats when (i = f || f = intIndex) -> 
          compare indices formats
      | _, [] -> (* There are more arguments *)
          ignore (warn "There are too many arguments for printf")

      | _ -> begin
          ignore (warn "Format string %a not compatible with arguments: %a\n" 
                    d_exp (mkString format_str)
                    docDescr descrt);
          raise Not_found
      end
    in
    compare indices format_indices;
    true
  with Not_found -> false

(** Remember here the functions that were called without a descriptor, so 
 * that we do not give more errors for the same function. *)
let callToVarargWithoutDescriptor: (string, unit) H.t = H.create 17
  
(* Prepare the arguments in a call to a vararg function *)
let prepareVarargArguments
    ~(mkTempVar: typ -> varinfo)
    ~(func: exp) 
    ~(nrformals: int)
    ~(args: exp list) : instr list * exp list = 
  try
    let descrt, isAuto = getVarargFunctionDescriptorType func in
    if debugVararg then 
      ignore (E.log "Preparing args in call to %a\n" d_exp func);
    let format_argo = getFormatArg func args in
    let nrargs = List.length args in
    let (_, indices, args', checkFormats) = 
      List.fold_right
        (fun a (arg_idx, indices, args, instrs) -> 
          if arg_idx > nrformals then begin
            let t = typeOf a in
            (* Search for a compatible type in the kinds *)
            let k_idx, _, kt, _ = 
              try findTypeIndex t descrt isAuto
              with Not_found ->  begin
                (* Maybe it is a format function. In that case cast to int *)
                if format_argo != None then begin
                  (* ignore (warn "Unexpected argument %d of format function %a. Turned into int.@!" arg_idx d_exp func)*)
                  try findTypeIndex intType descrt isAuto
                  with _ -> 
                    E.s (bug 
                           "the format descriptor %a does not have the int type for vararg function %a.@! Expected one of %a"
                           d_type descrt 
                           d_exp func
                           docDescr descrt)
                end else
                  E.s (error "Argument %d (%a : %a) does not match any expected type for vararg function %a.@! Expected one of %a" 
                         arg_idx d_exp a d_type t d_exp func 
                         docDescr descrt)
              end
            in
            (* Add an explicit cast from the actual argument to the type in 
             * the descriptor *)
            let a' = mkCastT a t kt in
            (* If this is a printf-function and this is a string argument we 
             * must convert it to string (and we must check it) *)
            let a'', instrs'' = 
              if format_argo != None && 
                 (match kt with TPtr _ -> true | _ -> false) 
              then begin
                (* Lookup the __stringof_ornull function.  This allows null 
		 * pointers to be passed as %s arguments. *) 
                let stringOf = 
                  try 
                    match H.find MU.allFunctions "__stringof_ornull" with 
                      MU.Declared fv -> fv
                    | _ -> E.s (bug "vararg: cannot find declaration of __stringof_ornull")
                  with Not_found -> 
                    E.s (bug "vararg: cannot find __stringof_ornull")
                in
                (* Make a new temporary variable *)
                let newarg = mkTempVar kt in 
                (* a' contains a cast to the type of the format argument. We 
                 * do not want the cast in the argument of __stringof_ornull.
                 * Thus, use "a" instead of a' *)
                let call = 
                  Call(Some (var newarg), Lval(var stringOf), 
                              [ a ],
                              !currentLoc)
                in
                Lval (var newarg), call :: instrs
              end else 
                a', instrs
            in
            (arg_idx - 1, (k_idx, kt) :: indices, a'' :: args, instrs'')
          end else
            (arg_idx - 1, indices, a :: args, instrs))
        args
        (nrargs, [], [], [])
    in
    if debugVararg then 
      ignore (E.log "Indices are: [%a]\n" 
                (docList 
                   (fun (idx, t) -> dprintf "%d:%a" idx d_type t)) indices);
    (* fetch the global variables *)
    let ccured_va_count, ccured_va_tags = fetchVarargGlobals () in
    (* Now construct the tag *)
    let rec loopIndices (count: int) (indices: (int * typ) list) 
        : exp (* a partial word*) * instr list (* set the following words 
        * *) = 
      match indices with 
      | [] -> zero, [Set(ccured_va_count, integer count, !currentLoc)]
      | (i, _) :: rest -> 
          let p_rest, rest = loopIndices (count + 1) rest in
          let amount = 8 * (count mod 4) in
          let shifted = 
            if amount = 0 then integer i else 
            BinOp(Shiftlt, integer i, integer amount, intType) in
          let bor_ed = 
            if isZero p_rest then shifted else 
            BinOp(BOr, shifted, p_rest, intType) in
          if amount = 0 then (* time to put into rest *)
            (zero,
             Set(addOffsetLval (Index(integer (count / 4), 
                                      NoOffset)) ccured_va_tags,
                 bor_ed, !currentLoc) :: rest) 
          else
            (bor_ed, rest)
    in
    (* Now check the special case of the format-functions with constant 
    * format strings *)
    let instr = 
      match format_argo with
      | Some format_arg -> begin
          match stripCasts format_arg with
            (Const(CStr format_str))
              when (checkFormatString format_str descrt indices) -> 
                [Set(ccured_va_count, integer (-1), !currentLoc)]
          | _ -> 
              (* format string not a constant or it cannot be checked 
               * statically. *)
              (* Generate code to fill in the indices *)
              let _, instr = loopIndices 0 indices in 
              (* Generate a call to a run-time function that checks the 
               * indices  *)
              let call = Call(None, Lval(var (get_checkFormatArgsFun())), 
                              [ format_arg ],
                              !currentLoc)
              in
              instr @ [call]
      end

      | None -> (* Not a printf function *)
          let _, instr = loopIndices 0 indices in 
          instr
    in
    checkFormats @ instr, args'
      
  with Not_found -> begin
    (* See if we have reported this one again *)
    let report = 
      match func with 
        Lval (Var vi, NoOffset) -> 
          if H.mem callToVarargWithoutDescriptor vi.vname then 
            false
          else begin
            H.add callToVarargWithoutDescriptor vi.vname ();
            true
          end
      | _ -> true
    in
    if report then 
      E.s (error "Call to vararg function %a without descriptor\n(additional calls with not be reported)\n"
             d_exp func)
    else (* We have already reported this one *)
      [], args
  end

(* Create the type for storing the vararg information.  This must match
   ccuredlib.c *)
let varargCompInfo: compinfo option ref = ref None
let getVarArgCompInfo () : compinfo  =  
  let ci = 
    match !varargCompInfo with 
      Some x -> x
    | None -> 
        let ci = 
          mkCompInfo true "__ccured_va_localinfo"
            (fun _ ->
              [ ("next", intType, None, [], !currentLoc);
                ("count", intType, None, [], !currentLoc);
                ("tags", TArray(intType, 
                                Some (integer ccured_va_count_max), []),
                         None, [], !currentLoc);
                ("nextp", voidPtrType, None, [], !currentLoc);
              ])
            [] in
        MU.theFile := GCompTag(ci, !currentLoc) :: !MU.theFile;
        varargCompInfo := Some ci;
        ci
  in
  ci

let hasTypeValist v: bool = 
  match unrollType v.vtype with 
    TPtr(TComp(ci, a), pa) when prefix "__ccured_va_list" ci.cname -> true
  | _ -> false

    (* The last formal in this body *)
let lastformal : (string * typ * attributes) ref = ref ("", voidType, [])

(** Now the handling of the body of vararg functions **)
class processVarargClass (fdec: fundec) = object
  inherit nopCilVisitor

    (* Change all call instructions to use the marker *)
  method vinst (i: instr) : instr list visitAction = 
    match i with 
      (* Make sure no one tampers with the va_list variables. 
       *  It is only legal to write to a va_list if the value being
       *  written comes from va_copy.*)
      Call(_, Lval(Var fvi, NoOffset), _, _) when
        fvi.vname = "__ccured_va_copy" -> 
          SkipChildren
    | (Set ((Var v, _), _, l)
       | Call(Some(Var v, _), _, _, l)) when hasTypeValist v ->
      E.s (error "Assignment to va_list is not allowed.  Use va_copy instead.\nCode is: %a" d_instr i)

    | Call(reso, (Lval(Var fvi, NoOffset) as f), args, l) -> 
	currentLoc := l;
        if fvi.vname = "__ccured_va_start" then begin
          let markerarg = 
            match args with 
              a1 :: _ -> a1
            | _ -> E.s (error "Call to __ccured_va_start with no arguments")
          in
          match stripCasts markerarg with 
            Lval (Var markervi, NoOffset) -> begin
              let markerdescrt, _ = 
                try getValistDescriptorType markervi fdec.svar
                with Not_found -> 
                  E.s (error "Call to va_start on a non va_list variable\n")
              in
              let fundescrt, isAuto = 
                try getVarargFunctionDescriptorType (Lval(var fdec.svar))
                with Not_found -> 
                  E.s (error "Call to va_start in a non vararg function\n")
              in
              if not isAuto && (typeSig markerdescrt) <> (typeSig fundescrt)
              then
                E.s (error "Cannot match the descriptor types in va_start");
              SkipChildren
            end
          | _ -> E.s (error "Invalid call to %s\n" fvi.vname)
        end else if "__ccured_va_arg" = fvi.vname then begin
          (* Find the type of the desired argument *)
          let markervi, desiredt = 
            match args with 
              Lval(Var markervi, NoOffset) :: SizeOf t :: _ :: [] 
              when not markervi.vglob -> 
                markervi, t
            | _ -> E.s (error "Invalid call to %s: %a" fvi.vname d_instr i)
          in
          (* Find the index in the union type of a compatible type *)
          let descrt, isAuto = 
            getValistDescriptorType markervi fdec.svar in
          let ki, kn, kt, ks = 
            try
              findTypeIndex desiredt descrt isAuto
            with Not_found -> begin
              let kinds = 
                try getVarargKinds descrt 
                with Not_found -> 
              E.s (error "Cannot find descriptor type in call to %s\n" fvi.vname)
              in
              E.s (error "Wasn't expecting (%a) for the \"type\" argument of va_arg.  Expecting a member of %a: %a.\n"
		     d_type (unrollType desiredt)
		     d_type descrt (* union *)
		     (docList ~sep:(chr ',' ++ break) 
                        (fun (_,_,tau,_) -> d_type () tau)) kinds)
            end
          in
          (* Now change the type of the temporary variable that takes this 
           * result to a pointer to kt *)
          (match reso with 
            Some (Var tmpvi, NoOffset) -> 
              tmpvi.vtype <- TPtr(kt,[])
          | None -> ignore (warn "Call to va_arg is not assigned")
          | _ -> E.s (unimp "Result of va_arg does not go into a variable"));
          (* it is important that the argument of sizeof shares the node with 
           * the actualy union field *)
          ChangeTo ([Call(reso, f, [ Lval (var markervi); 
                                     SizeOf kt; 
                                     integer ki ], l)])
        end else
          SkipChildren
    | _ -> SkipChildren
end


(** Make sure you call this before marking anything in the function body. If 
 * you do not do that the newly created temporaries might not get marked *)
let processVarargBody (fdec: fundec) : unit = 
  let formals, isva = 
    match fdec.svar.vtype with
      TFun(_, formals, isva, _) -> formals, isva
    | _ -> E.s (E.bug "Function does not have function type")
  in
  let foundVarargs = ref false in
  (* Get and memoize the descriptor for a va_list local. Return None if this 
   * is not a va_list local. *)
  let getDescriptorLocal (l: varinfo) : typ option = 
    if hasTypeValist l then begin
        foundVarargs := true;
        if l.vaddrof then
          E.s (error "You may not take the address of va_list variable %s"
                 l.vname);
        let descrt, isAuto = 
          try getValistDescriptorType l fdec.svar
          with Not_found -> begin
            E.s (error 
                   "Cannot find the descriptor type for va_list local %s in %s"
                   l.vname fdec.svar.vname)
          end
        in
        if debugVararg then 
          ignore (E.log "va: found va_list variable %s with descriptor %a\n"
                    l.vname d_type descrt);
        Some descrt
    end
    else
      None
  in
  let doLocal (acc: instr list) 
              (l: varinfo) = 
    (* Get and memoize the descriptor type. We'll need it later *)
    match getDescriptorLocal l with 
    | Some descrt -> 
        (* Make a local to store the va info *)
        let ci = getVarArgCompInfo () in
        let vainfo = 
          makeTempVar fdec ~name:(l.vname ^ "__vainfo") (TComp(ci, [])) in
        vainfo.vaddrof <- true;
        if debugVararg then 
          ignore (E.log "va: creating local va_local %s for %s\n"
                    vainfo.vname l.vname);
        (* And an instruction to initialize the pointer *)
        let init = Set(var l, AddrOf (var vainfo), l.vdecl) in
        (* And one to initialize the vainfo struct itself *)
        let init2 = Call(None, Lval(var(get_vaInitFun())),
                         [Lval (var l)], l.vdecl) in
        init :: init2 :: acc
    | None ->
        acc
  in
  (* Go through all the locals (but not formals) and when we see a variable 
   * of type __ccured_va_list then we allocate a local structure to which the 
   * variable should point *)
  let initlocals = List.fold_left doLocal [] fdec.slocals in
  (* Go through the formals also, to verify that they have descriptors *)
  List.iter (fun f -> ignore (getDescriptorLocal f)) fdec.sformals;
  if !foundVarargs then begin
    lastformal := 
       if isva then begin
         (* Get the last formal *)
         let rec getlast = function 
             [] -> E.s (E.bug "Vararg function %s does not have formals" 
                          fdec.svar.vname)
           | [l] -> l
           | _ :: rest -> getlast rest
         in getlast (argsToList formals)
       end else ("", voidType, []);
    let oldloc = !currentLoc in
    let va_visit = new processVarargClass(fdec) in
    fdec.sbody <- visitCilBlock va_visit fdec.sbody;
    currentLoc := oldloc;
    (* Now insert code to initialize the next fields *)
    fdec.sbody.bstmts <- 
       mkStmt (Instr initlocals) ::
       fdec.sbody.bstmts
  end


let markPrintfFunction (funType:typ) (format_idx: int) : typ = 
begin
  let oldAttrs = typeAttrs funType in
  (* Check for duplicatate vararg specifiers *)
  begin
    match filterAttributes "ccuredformat" oldAttrs with
      [Attr(_, [AInt oldidx])] ->
	if oldidx <> format_idx then 
	  ignore (warn "Duplicate vararg:printf declaration for %a. First with index %d and now with %d.\n" d_type funType oldidx format_idx)
    | [] -> 
	begin
	  match filterAttributes "ccuredvararg" oldAttrs with
	    [] -> ()  (*good. no previous format specifiers *)
	  | _ ->
	      ignore (warn "%a previously declared with a custom vararg type, now declared printf-like.\n" d_type funType)
	end
    | al -> E.s (bug "Don't understand %a" d_attrlist al)
  end;

  (* See if the declared format argument has "char *" type *)
  if format_idx <= 0 then 
    E.s (error "The format argument index must be >= 1");
  let _, args, _, _ = splitFunctionType funType in
  let args' = argsToList args in
  if List.length args' < format_idx then 
    E.s (error "The format argument index must be <= #arguments");
  let format_type = 
    match List.nth args' (format_idx - 1) with 
      (_, t, _) -> t 
  in
  let format_type_ok = 
    match unrollType format_type with
      TPtr(t, _) -> begin
        match unrollType t with 
          TInt((IChar|IUChar|ISChar), _) -> true
        | _ -> false
      end
    | _ -> false
  in
  if not format_type_ok then
    E.s (error "The declared format argument (%d) has wrong type: %a\nThe function has type:@!%a\n"
           format_idx d_type format_type
           d_type funType);
    (* weimer: I needed this error message to be more verbose for bind *)

  let newType = typeAddAttributes 
    [(Attr("ccuredvararg", [ASizeOf (getPrintfFormatStruct ())]));
     (Attr("ccuredformat", [AInt format_idx]))]
    funType in
  newType
end

    
let markPrintfFunctionByName (s: string) (format_idx: int) =
  try
    let oldidx = H.find printfFunctionsByName s in
    if oldidx <> format_idx then 
      ignore (warn "Duplicate ccuredvararg(printf) declaration for %s. First with index %d and now with %d.\n" s oldidx format_idx);
  with Not_found -> begin
    H.add printfFunctionsByName s format_idx;
    if !E.verboseFlag then 
      ignore (E.log "Will treat %s as a printf-like function\n" s);
    MU.applyToFunction s 
      (fun vi -> 
	vi.vtype <- markPrintfFunction vi.vtype format_idx)
  end

let markVarargFunction (s: string) (t: typ) = 
  try
    let oldt = H.find varargFunctions s in
(* This check gives false alarms
    if typeSig oldt <> typeSig t then 
      ignore (E.warn "Duplicate ccuredvararg declaration for %s\n" s);
*)
    ()
  with Not_found -> begin
    H.add varargFunctions s t;
    if H.mem printfFunctionsByName s then 
      ignore (E.warn "Function %s has already been declared vararg_printf\n" 
                s);
    (* Check the type *)
    if (try 0 = bitsSizeOf t with _ -> true) then 
      ignore (E.warn "Vararg descriptor for %s has an incomplete type %a\n" s d_type t);
    let kinds = getVarargKinds t in
    (* Make sure that no two types are compatible *)
    let _ = 
      List.fold_left
        (fun prev ((_, thisn, _, thiss) as this) -> 
          List.iter
            (fun (_, pn, pt, ps) -> 
              if thiss = ps then 
                E.s (error "Vararg type %a has compatible fields %s and %s\n"
                       d_type t pn thisn)) prev;
          this :: prev)
        []
        kinds
    in

    if debugVararg then 
      if !E.verboseFlag then 
        ignore (E.log "Will treat %s as a vararg function\n" s);
    MU.applyToFunction s 
      (fun fvi -> 
        if not (hasAttribute "ccuredvararg" 
                  (MU.getFunctionTypeAttributes (Lval(Var fvi, NoOffset)))) 
        then 
          MU.addFunctionTypeAttribute 
            (Attr("ccuredvararg", [ASizeOf t]))
            fvi)
  end
  
(* First process the pragmas *)
let processPragma (a: attribute) : unit = 
  match a with 
  | Attr("ccuredvararg", [AStr s; ASizeOf t]) ->
      markVarargFunction s t

  | Attr("ccuredvararg", [AStr s; ACons("printf", [AInt format_idx])]) -> 
      markPrintfFunctionByName s format_idx

  | Attr("ccuredvararg", _) -> 
      E.s (error "Bad syntax in #pragma ccuredvararg")

  | _ -> ()

(* Turn the gcc format attribute into our own notation.  Returns a type
   that may have a new attribute but which is otherwise the same. *)
let processFormatAttribute (funType: typ) : typ = 
  match filterAttributes "format" (typeAttrs funType)
        @ filterAttributes "__format__" (typeAttrs funType)
  with
    [Attr(_, [printf; AInt format_idx; AInt _]) as a] 
      when (match printf with 
                ACons("printf",[])  
              | ACons("__printf__",[]) -> true 
              | _ -> false) -> 
      markPrintfFunction funType format_idx

  | [] -> funType
  | al -> ignore (warn "Do not understand %a" d_attrlist al); funType


let initFile () :unit = 
  H.clear varargFunctions;
  H.clear printfFunctionsByName;
  H.clear callToVarargWithoutDescriptor;
  H.clear autoDescr;
  ()


let addToFileAutoDescr () : unit = 
  (* For each of the automatically generated descriptors, emit a structure 
   * definition *)
  H.iter 
    (fun s (vi,ci) -> 
      ignore (E.warn "Generated automatic vararg descriptor for %s at %a:@! %a@!  If this is a printf-like function you should declare it!"
                s d_loc vi.vdecl docDescr (TComp(ci, [])));
      MU.theFile := GCompTag(ci, locUnknown) :: !MU.theFile)
    autoDescr;
  initFile ();


