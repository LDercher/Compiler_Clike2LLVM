module Compiler where

import Clike.Language as Clike
import Clike.Text as Clike
import LL.Language as LL
import LL.Text as LL
import Text

import Data.List

import Debug.Trace

{-------------------------------------------------------------------------------

Entry point: compile Clike programs into LLVM programs.

Note: there is significant overlap of constructor names between the LLVM and
Clike syntax trees.  You should prefix constructors with LL. or Clike. to
distinguish them.

-------------------------------------------------------------------------------}

compileProgram :: Clike.Prog -> LL.Prog
compileProgram fdecls = P { types = [], globals = [], functions = map compileFunction fdecls, externs = [] }

{-------------------------------------------------------------------------------

Compiles Clike functions into LLVM functions.

This is the starting point of your implementation.  So long as this bit
corresponds to the results of the interpreter, you'll receive credit.

-------------------------------------------------------------------------------}

compileFunction :: Clike.TopDecl -> (String, LL.Function)
compileFunction = error "unimplemented"



compileStatements :: [Clike.Stmt] -> String -> String -> String -> Int -> (([(String, LL.Block)], String), Int)
compileStatements stmts continueLabel breakLabel nextBlockLabel i =
    foldr (\stmt ((blocks, nextBlockLabel), i) ->
               let ((blocks', entry), i') = compileStatement stmt continueLabel breakLabel nextBlockLabel i in
               ((blocks' ++ blocks, entry), i'))
          (([], nextBlockLabel), i)
          stmts

{-------------------------------------------------------------------------------

My compileStatement function has the following interpretation:

    compileStatement stmt continueLabel breakLabel nextBlockLabel i

`stmt` is the statement to be compiled.  `continueLabel` is the label to jump to
in case of a continue.  `breakLabel` is the label to jump to in case of a break.
`nextBlockLabel` is the label to jump to should control exit normally.  Finally,
`i` is an integer used to generate fresh names.

My compileStatement returns three things: a list of blocks generated, the label
to use to enter those blocks, and finally the updated integer after generating
fresh names.

-------------------------------------------------------------------------------}


compileStatement :: Clike.Stmt -> String -> String -> String -> Int -> (([(String, LL.Block)], String), Int)
compileStatement  (Clike.ExpS e) continueLabel nextBlockLabel breakLabel i = (([((show nextI),(insts, Ret I64 op)],(show nextI), nextI)
                                                                                    where ((insts, op), nextI) = compileExpression e i
compileStatement (If exp s1 s2) continueLabel nextBlockLabel breakLabel i = (([((show i3),(insts ++ [Icmp (show i) LL.Eq I64 op (LL.Const 0)],CBr op name1 name2))] ++ block1 ++ block2,(show i3)), i3)
                                                                                    where ((insts, op), nextI) = compileExpression exp i
                                                                                          ((block1, name1), i'') = compileStatement s1 continueLabel nextBlockLabel breakLabel nextI
                                                                                          ((block2, name2), i3) = compileStatement s2 continueLabel nextBlockLabel breakLabel i''
                                                                        

{-------------------------------------------------------------------------------

compileExpression is simpler than compileStatement, because you don't have to
worry about flow of control.  You do, however, have to worry about un-nesting
nested expressions.  In the type below, the Int argument is for generating fresh
names.  The result includes the sequence of instructions used to compute the
expression, the LLVM operand containing the result of the expression, and the
updated integer after generating fresh names.  For example, suppose you had:

    compileExpression (Bin Plus (Bin Times (OpE (Const 3))
                                           (OpE (Const 5)))
                                (OpE (Const 6))
                      4

I would expect this to produce results similar to:

    (([LL.Bin "__x4" LL.Times (LL.Const 3) (LL.Const 5),
       LL.Bin "__x5" LL.Times (LL.Uid "__x4") (LL.Const 6)],
      LL.Uid "__x5"),
     6)

-------------------------------------------------------------------------------}


compileExpression :: Clike.Expr -> Int -> (([LL.Instruction], LL.Operand), Int)
compileExpression (OpE op) i = compileOperand op (i+1)
compileExpression (Clike.Bin binOptr exp1 exp2) i = ((op1Insts ++ op2Insts ++ [insts], operand), i2+1)
                where ((op1Insts, op1Lop), i1) = compileExpression exp1 i
                      ((op2Insts, op2Lop), i2) = compileExpression exp2 i1
                      (operand, insts) = inst binOptr
                      inst Plus = (Uid (show i2), LL.Bin (show i2) Add I64 op1Lop op2Lop)
                      inst Minus = (Uid (show i2), LL.Bin (show i2) Sub I64 op1Lop op2Lop)
                      inst Times = (Uid (show i2), LL.Bin (show i2) Mul I64 op1Lop op2Lop)
                      inst Clike.And  = (Uid (show i2), LL.Bin (show i2) LL.And I64 op1Lop op2Lop)
                      inst Clike.Or = (Uid (show i2), LL.Bin (show i2) LL.Or I64 op1Lop op2Lop)
                      inst Clike.Xor = (Uid (show i2), LL.Bin (show i2) LL.Xor I64 op1Lop op2Lop)
                      inst Clike.Shl = (Uid (show i2), LL.Bin (show i2) LL.Shl I64 op1Lop op2Lop)
                      inst Clike.Ashr = (Uid (show i2), LL.Bin (show i2) LL.Ashr I64 op1Lop op2Lop)
                      inst Clike.Lshr = (Uid (show i2), LL.Bin (show i2) LL.Lshr I64 op1Lop op2Lop)
                      inst Clike.Eq = (Uid (show i2), LL.Icmp (show i2) LL.Eq I64 op1Lop op2Lop)
                      inst Clike.Neq = (Uid (show i2), LL.Icmp (show i2) LL.Neq I64 op1Lop op2Lop)
                      inst Clike.Lt = (Uid (show i2), LL.Icmp (show i2) LL.Lt I64 op1Lop op2Lop)
                      inst Clike.Lte = (Uid (show i2), LL.Icmp (show i2) LL.Le I64 op1Lop op2Lop)
                      inst Clike.Gt = (Uid (show i2), LL.Icmp (show i2) LL.Gt I64 op1Lop op2Lop)
                      inst Clike.Gte = (Uid (show i2), LL.Icmp (show i2) LL.Ge I64 op1Lop op2Lop)
                      inst Clike.Assign = (op2Lop, LL.Store I64 op1Lop op2Lop)
compileExpression (Unary Negate exp) i = (([LL.Bin (show i1) Mul I64 opLop (LL.Const (-1))], (Uid (show i1))), i1+1)
                    where ((opinsts, opLop), i1) = compileExpression exp i
compileExpression (Unary Complement exp ) i = (([LL.Bin (show i1) LL.Xor I64 opLop (LL.Const (-1))], (Uid (show i1))), i1+1)
                    where ((opIntrs, opLop), i1) =  compileExpression exp i
compileExpression (Clike.Call s exps) i = ((insts ++ [LL.Call (show i) I64 s ( map (\ops -> (I64,ops)) argOps)], Uid (show i)), i+1)
                    where (insts, argOps, i') = compileArgs exps i
                          compileArgs (arg:args) i = (insts ++ insts', op:ops, i'')
                                where ((insts, op), i') = compileExpression arg i'
                                      (insts', ops, i'') = compileArgs args i'












{-------------------------------------------------------------------------------

compileOperand has identical behavior to compileExpression.  Note that, as Clike
variables support assignment, unlike LLVM temporaries, you will need to store
your Clike variables on the stack and use Store/Load to get to them.

-------------------------------------------------------------------------------}


compileOperand :: Clike.Operand -> Int -> (([LL.Instruction], LL.Operand), Int)
compileOperand (Var s) i  = (([(Load (show i) I64 (Uid s))],Uid (show i)), i+1)
compileOperand (Clike.Const i64) i = (([ (Load (show i) I64 (Uid (show i)))], Uid (show i)), i+1)
compileOperand (Dot o s) i = error "i"



{--

CLike:
data Operand = Var String | Const Int64 | Dot Operand String
  deriving (Eq, Show)

  data Operand = Const Int64 | Gid String | Uid String
  deriving (Eq, Read, Show)

LLVMLite:
data Instruction
    = Bin String Operator Type Operand Operand  -- %uid = binop t op, op
    | Alloca String Type                        -- %uid = alloca t
    | Load String Type Operand                  -- %uid = load t, t* op
    | Store Type Operand Operand                -- store t op1, t* op2
    | Icmp String Condition Type Operand Operand -- %uid = icmp rel t op1 op2
    | Call String Type String [(Type, Operand)] -- %uid = call ret_ty name(t1 op1, t2 op2, ...)
    | Bitcast String Type Operand Type          -- %uid = bitcast t1 op to t2
    | Gep String Type Operand [Operand]         -- %uid = getelementptr t op, i64 op1, i64 op2
                                                --    .. or i32, if accessing struct...
  deriving (Eq, Read, Show)
  --}