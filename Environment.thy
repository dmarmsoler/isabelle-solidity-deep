section\<open>Environment and State\<close>
theory Environment
imports Accounts Storage StateMonad
begin

subsection \<open>Environment\<close>

datatype Type = Value Types
              | Calldata MTypes
              | Memory MTypes
              | Storage STypes
 
datatype Denvalue = Stackloc Location
                  | Storeloc Location

type_synonym Identifier = String.literal
 
record Environment =
  address :: Address (*address of executing contract*)
  sender :: Address (*address of calling contract*)
  svalue :: Valuetype (*money send*)
  denvalue :: "(Identifier, Type \<times> Denvalue) fmap" 
 
fun identifiers :: "Environment \<Rightarrow> Identifier fset"
  where "identifiers e = fmdom (denvalue e)"
 
fun emptyEnv :: "Address \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> Environment"
  where "emptyEnv a s v = \<lparr>address = a, sender = s, svalue =v, denvalue = fmempty\<rparr>"
 
definition eempty :: "Environment"
  where "eempty = emptyEnv (STR '''') (STR '''') (STR '''')"

declare eempty_def [solidity_symbex]

fun updateEnv :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnv i t v e = e \<lparr> denvalue := fmupd i (t,v) (denvalue e) \<rparr>"

fun updateEnvOption :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment option"
  where "updateEnvOption i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> None
            | None \<Rightarrow> Some (updateEnv i t v e))"

lemma updateEnvOption_address: "updateEnvOption i t v e = Some e' \<Longrightarrow> address e = address e'"
by (auto split:option.split_asm)

fun updateEnvDup :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnvDup i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> e
            | None \<Rightarrow> updateEnv i t v e)"

lemma updateEnvDup_address[simp]: "address (updateEnvDup i t v e) = address e"
  by (auto split:option.split)

lemma updateEnvDup_sender[simp]: "sender (updateEnvDup i t v e) = sender e"
  by (auto split:option.split)

lemma updateEnvDup_svalue[simp]: "svalue (updateEnvDup i t v e) = svalue e"
  by (auto split:option.split)

lemma updateEnvDup_dup:
  assumes "i\<noteq>i'" shows "fmlookup (denvalue (updateEnvDup i t v e)) i' = fmlookup (denvalue e) i'"
proof (cases "fmlookup (denvalue e) i = None")
  case True
  then show ?thesis using assms by simp
next
  case False
  then obtain e' where "fmlookup (denvalue e) i = Some e'" by auto
  then show ?thesis using assms by simp
qed

lemma env_reorder_neq:
  assumes "x\<noteq>y"
  shows "updateEnv x t1 v1 (updateEnv y t2 v2 e) = updateEnv y t2 v2 (updateEnv x t1 v1 e)"
proof -
  have "address (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = address (updateEnv y t2 v2 (updateEnv x t1 v1 e))" by simp
  moreover from assms have "denvalue (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = denvalue (updateEnv y t2 v2 (updateEnv x t1 v1 e))" using Finite_Map.fmupd_reorder_neq[of x y "(t1,v1)" "(t2,v2)"] by simp
  ultimately show ?thesis by simp
qed

lemma uEO_in:
  assumes "i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = None"
  using assms by auto

lemma uEO_n_In:
  assumes "\<not> i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = Some (updateEnv i t v e)"
  using assms by auto

fun astack :: "Identifier \<Rightarrow> Type \<Rightarrow> Stackvalue \<Rightarrow> Stack * Environment \<Rightarrow> Stack * Environment"
  where "astack i t v (s, e) = (push v s, (updateEnv i t (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc s))) e))"

subsubsection \<open>Examples\<close>
abbreviation "myenv::Environment \<equiv> eempty \<lparr>denvalue := fmupd STR ''id1'' (Value TBool, Stackloc STR ''0'') fmempty\<rparr>"
abbreviation "mystack::Stack \<equiv> \<lparr>mapping = fmupd (STR ''0'') (KValue STR ''True'') fmempty, toploc = 1\<rparr>"

abbreviation "myenv2::Environment \<equiv> eempty \<lparr>denvalue := fmupd STR ''id2'' (Value TBool, Stackloc STR ''1'') (fmupd STR ''id1'' (Value TBool, Stackloc STR ''0'') fmempty)\<rparr>"
abbreviation "mystack2::Stack \<equiv> \<lparr>mapping = fmupd (STR ''1'') (KValue STR ''False'') (fmupd (STR ''0'') (KValue STR ''True'') fmempty), toploc = 2\<rparr>"

lemma "astack (STR ''id1'') (Value TBool) (KValue (STR ''True'')) (emptyStore, eempty) = (mystack,myenv)" by solidity_symbex
lemma "astack (STR ''id2'') (Value TBool) (KValue (STR ''False'')) (mystack, myenv) = (mystack2,myenv2)" by solidity_symbex

subsection \<open>Declarations\<close>

text \<open>This function is used to declare a new variable: decl id tp val copy cd mem sto c m k e
\begin{description}
  \item[id] is the name of the variable
  \item[tp] is the type of the variable
  \item[val] is an optional initialization parameter. If it is None, the types default value is taken.
  \item[copy] is a flag to indicate whether memory should be copied (from mem parameter) or not (copying is required for example for external method calls).
  \item[cd] is the original calldata which is used as a source
  \item[mem] is the original memory which is used as a source
  \item[sto] is the original storage which is used as a source
  \item[c] is the new calldata which is updated
  \item[m] is the new memory which is updated
  \item[k] is the new calldata which is updated
  \item[e] is the new environment which is updated
\end{description}\<close>
fun decl :: "Identifier \<Rightarrow> Type \<Rightarrow> (Stackvalue * Type) option \<Rightarrow> bool \<Rightarrow> CalldataT \<Rightarrow> MemoryT \<Rightarrow> ((Address, StorageT) fmap)
    \<Rightarrow> CalldataT \<times> MemoryT \<times> Stack \<times> Environment \<Rightarrow> (CalldataT \<times> MemoryT \<times> Stack \<times> Environment) option"
  where
(* Declaring stack variables *)
  "decl i (Value t) None _ _ _ _ (c, m, k, e) = Some (c, m, (astack i (Value t) (KValue (ival t)) (k, e)))"
| "decl i (Value t) (Some (KValue v, Value t')) _ _ _ _ (c, m, k, e) =
   Option.bind (convert t' t v)
    (\<lambda>(v', t''). Some (c, m, astack i (Value t'') (KValue v') (k, e)))"
| "decl _ (Value _) _ _ _ _ _ _ = None"

(* Declaring calldata variables *)
| "decl i (Calldata (MTArray x t)) (Some (KCDptr p, _)) True cd _ _ (c, m, k, e) =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in Option.bind (cpm2m p l x t cd c')
      (\<lambda>c''. Some (c'', m, astack i (Calldata (MTArray x t)) (KCDptr l) (k, e))))"
| "decl i (Calldata (MTArray x t)) (Some (KMemptr p, _)) True _ mem _ (c, m, k, e) =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in Option.bind (cpm2m p l x t mem c')
      (\<lambda>c''. Some (c'', m, astack i (Calldata (MTArray x t)) (KCDptr l) (k, e))))"
| "decl i (Calldata _) _ _ _ _ _ _ = None"

(* Declaring memory variables *)
| "decl i (Memory (MTArray x t)) None _ _ _ _ (c, m, k, e) =
    (let m' = minit x t m
      in Some (c, m', astack i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e)))"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, _)) True _ mem _ (c, m, k, e) =
   Option.bind (cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t mem (snd (allocate m)))
    (\<lambda>m'. Some (c, m', astack i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e)))"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, _)) False _ _ _ (c, m, k, e) =
   Some (c, m, astack i (Memory (MTArray x t)) (KMemptr p) (k, e))"
| "decl i (Memory (MTArray x t)) (Some (KCDptr p, _)) _ cd _ _ (c, m, k, e) =
   Option.bind (cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t cd (snd (allocate m)))
    (\<lambda>m'. Some (c, m', astack i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e)))"
| "decl i (Memory (MTArray x t)) (Some (KStoptr p, Storage (STArray x' t'))) _ _ _ s (c, m, k, e) =
    Option.bind (fmlookup s (address e))
      (\<lambda>s'. Option.bind (cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x' t' s' (snd (allocate m)))
        (\<lambda>m''. Some (c, m'', astack i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e))))"
| "decl _ (Memory _) _ _ _ _ _ _ = None"

(* Declaring storage variables *)
| "decl i (Storage (STArray x t)) (Some (KStoptr p, _)) _ _ _ _ (c, m, k, e) =
    Some (c, m, astack i (Storage (STArray x t)) (KStoptr p) (k, e))"
| "decl i (Storage (STMap t t')) (Some (KStoptr p, _)) _ _ _ _ (c, m, k, e) =
   Some (c, m, astack i (Storage (STMap t t')) (KStoptr p) (k, e))"
| "decl _ (Storage _) _ _ _ _ _ _ = None" (* Uninitialized storage arrays/maps not allowed *)

lemma decl_address:
  assumes "decl a1 a2 a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "address env = address env' \<and> sender env = sender env' \<and> svalue env = svalue env'"
  using assms
proof (cases rule:decl.elims)
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    show ?thesis
    proof (cases a)
      case p2: (Pair a b)
      with 2 s show ?thesis by simp
    qed
  qed
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c'")
    case None
    with 9 l_def c_def show ?thesis by simp
  next
    case s2: (Some a)
    with 9 l_def c_def show ?thesis by simp
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c'")
    case None
    with 10 l_def c_def show ?thesis by simp
  next
    case s2: (Some a)
    with 10 l_def c_def show ?thesis by simp
  qed
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m'")
      case None
      with 19 l_def m'_def show ?thesis by simp
    next
      case s2: (Some a)
      with 19 l_def m'_def show ?thesis by simp
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m'")
    case None
    with 21 l_def m'_def show ?thesis by simp
  next
    case s2: (Some a)
    with 21 l_def m'_def show ?thesis by simp
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
  from 22 l_def m'_def
  obtain s' where *: "fmlookup s (address env) = Some s'" by fastforce
  then show ?thesis
  proof (cases "cps2m p l x' t' s' m'")
    case None
    with 22 l_def m'_def * show ?thesis by simp
  next
    case s2: (Some a)
    with 22 l_def m'_def * show ?thesis by simp
  qed
qed (simp_all)

end
