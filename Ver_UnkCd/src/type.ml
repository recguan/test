
type name = string
type exp = Var of name 
  | LVar of name 
  | SVar of name 
  | Ref of exp 
  | Nil
type pure = Eq of exp * exp 
  | Neq of exp * exp 
  | PTop
type purelist = pure list
type sep = Point of exp * exp 
  | Lseg of exp * exp 
  | Junk | Emp | STop
type seplist = sep list
type heap = SH of purelist * seplist 
  | Top

type atom = Assign of exp * exp 
  | Disp of exp 
  | New of exp * exp 
  | Skip 
  | Assume of heap 
  | Assert of heap

type constr = Atom of atom 
  | Fun of name * exp list * exp list * heap * heap 
  | Seq of constr list 
  | If of pure * constr * constr 
  | CWhile of pure * constr

type unkblk = UnkFun of name * exp list * exp list 
  | If_l of pure * unkseg * constr  
  | If_r of pure * constr * unkseg  
  | If_b of pure * unkseg * unkseg 
  | UWhile of pure * unkseg 

and unkseg = V of constr * unkblk * exp list * exp list * constr * exp list * exp list

type allspec = Spec of name * heap * heap
