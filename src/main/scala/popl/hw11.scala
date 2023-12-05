package popl

object hw11 extends js.util.JsApp:
  import js.ast._
  import js._
  import js.util.State
  import Uop._, Bop._, Typ._, Mut._
  /*
   * CSCI-UA.0480-055: Homework 11
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your hw11 object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your solution will _not_ be graded if it does not compile!!
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * '???' as needed to get something that compiles without error.
   *
   */

  /* Type Inference */
  
  // A helper function to check whether a JS type has a function type in it.
  def hasFunctionTyp(t: Typ): Boolean = t match
    case TFunction(_, _) => true
    case TObj(fes) => fes exists { case (_, (_, t)) => hasFunctionTyp(t) }
    case _ => false
    
  def typeInfer(env: Map[String, (Mut, Typ)], e: Expr): Typ =
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1)
    def locerr[T](e1: Expr): T = throw LocTypeError(e1)
    def checkTyp(texp: Typ, e1: Expr): Typ =
      val tgot = typ(e1)
      if texp == tgot then texp else err(tgot, e1)
    
    e match
      case Print(e1) => typ(e1); TUndefined
      
      case Num(_) => TNumber
      
      case Bool(_) => TBool
      
      case Undefined => TUndefined
      
      case Str(_) => TString
      
      case Var(x) => env(x)._2
      
      case Decl(mut, x, e1, e2) => 
        typeInfer(env + (x -> (mut, typ(e1))), e2)
      
      case UnOp(UMinus, e1) => typ(e1) match
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      
      case UnOp(Not, e1) =>
        checkTyp(TBool, e1)
      
      case UnOp(FldDeref(f), e) => typ(e) match
        case TObj(tfs) if tfs contains f => tfs(f)._2
        case tgot => err(tgot, e)
        
      case BinOp(bop, e1, e2) =>
        bop match
          case Plus =>
            typ(e1) match
              case TNumber => checkTyp(TNumber, e2)
              case TString => checkTyp(TString, e2)
              case tgot => err(tgot, e1)
      
          case Minus | Times | Div => 
            checkTyp(TNumber, e1)
            checkTyp(TNumber, e2)
          
          case Eq | Ne => typ(e1) match
            case t1 if !hasFunctionTyp(t1) => 
              checkTyp(t1, e2); TBool
            case tgot => err(tgot, e1)
          
          case Lt | Le | Gt | Ge =>
            typ(e1) match
              case TNumber => checkTyp(TNumber, e2)
              case TString => checkTyp(TString, e2)
              case tgot => err(tgot, e1)
            TBool
          
          case And | Or =>
            checkTyp(TBool, e1)
            checkTyp(TBool, e2)
          
          case Seq =>
            typ(e1); typ(e2)
          
          case Assign =>
            e1 match
              case Var(x) =>
                env(x) match
                  case (MLet, t) => checkTyp(t, e2)
                  case _ => locerr(e1)
          
              case UnOp(FldDeref(f), e11) =>
                val t11 = typ(e11)
                t11 match
                  case TObj(tfs) if tfs contains f =>
                    val (mut, t1) = tfs(f)
                    mut match
                      case MLet => checkTyp(t1, e2)
                      case MConst => locerr(e1)
                  case _ => err(t11, e11)
              
              case _ => locerr(e1)
        
      case If(e1, e2, e3) =>
        checkTyp(TBool, e1)
        val t2 = typ(e2)
        checkTyp(t2, e3)
      
      case Function(p, xs, tann, e1) =>
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(xs map (_._2), tret)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        // Bind to env2 an environment that extends env1 with bindings for xs.
        val env2 = xs.foldLeft(env1){ 
          case (env2, (x, t)) => env2 + (x -> (MConst, t))
        }
        // Match on whether the return type is specified.
        tann match
          case None => TFunction(xs map (_._2), typeInfer(env2, e1))
          case Some(tret) => 
            typeInfer(env2, e1) match
              case tbody if tbody == tret => 
                TFunction(xs map (_._2), tret)
              case tbody => err(tbody, e1)

      case Call(e1, es) => typ(e1) match
        case TFunction(txs, tret) if txs.length == es.length =>
          txs.lazyZip(es).foreach(checkTyp)
          tret
        case tgot => err(tgot, e1)
      
      case ObjLit(fs) => TObj(fs transform { case (_, (mut, e)) => (mut, typ(e)) })
      
      case Addr(_) | UnOp(Deref, _) =>
        throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
  
  /* JakartaScript Interpreter */
  
  def toNum(v: Val): Double = v match
    case Num(n) => n
    case _ => throw StuckError(v)
  
  def toBool(v: Val): Boolean = v match
    case Bool(b) => b
    case _ => throw StuckError(v)
  
  def toStr(v: Val): String = v match
    case Str(s) => s
    case _ => throw StuckError(v)

  def toAddr(v: Val): Addr = v match
    case a: Addr => a
    case _ => throw StuckError(v)

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Val, v2: Val): Boolean =
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match
      case (Str(s1), Str(s2)) =>
        (bop: @unchecked) match
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
      case _ =>
        val (n1, n2) = (toNum(v1), toNum(v2))
        (bop: @unchecked) match
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
    
  /* 
   * Substitutions e[er/x]
   */
  def subst(e: Expr, x: String, er: Expr): Expr =
    require(closed(er))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def substX(e: Expr): Expr = subst(e, x, er)
    /* Body */
    e match
      case Num(_) | Bool(_) | Undefined | Str(_) | Addr(_) => e
      case Var(y) => 
        if x == y then er.clone(e.pos) else e
      case e@Print(e1) => 
        e.copy(e1 = substX(e1)).setPos(e.pos)
      case e@UnOp(uop, e1) => 
        e.copy(e1 = substX(e1)).setPos(e.pos)
      case e@BinOp(bop, e1, e2) => 
        e.copy(e1 = substX(e1), e2 = substX(e2)).setPos(e.pos)
      case e@If(e1, e2, e3) => 
        e.copy(e1 = substX(e1), e2 = substX(e2), e3 = substX(e3))
      case e@Call(e0, es) =>
        e.copy(e0 = substX(e0), es = es map substX).setPos(e.pos)
      case e@Decl(mut, y, ed, eb) => 
        e.copy(ed = substX(ed), eb = if x == y then eb else substX(eb)).setPos(e.pos)
      case e@Function(p, ys, tann, eb) => 
        if p.contains(x) || (ys exists (_._1 == x)) then e 
        else e.copy(e = substX(eb)).setPos(e.pos)
      case e@ObjLit(fes) => 
        e.copy(fes = fes transform { case (_, (m, e)) => (m, substX(e)) }).setPos(e.pos)

  
  /*
   * Big-step interpreter.
   */
  def eval(e: Expr): State[Mem, Val] =
    require(closed(e), "eval called on non-closed expression:\n" + e.prettyJS)
    /* Some helper functions for convenience. */
    def eToNum(e: Expr): State[Mem, Double] =
      for ( v <- eval(e) ) yield toNum(v)
    def eToBool(e: Expr): State[Mem, Boolean] = 
       for ( v <- eval(e) ) yield toBool(v)
    def eToAddr(e: Expr): State[Mem, Addr] = 
       for ( v <- eval(e) ) yield toAddr(v)
    def readVal(a: Addr): State[Mem, Val] = 
      State.read { (m: Mem) =>
        m(a) match
          case v: Val => v
          case _ => throw StuckError(e)
      }
    def readObj(a: Addr): State[Mem, Map[String, Val]] = 
      State.read { (m: Mem) =>
        m(a) match
          case Obj(fs) => fs
          case _ => throw StuckError(e)
      }
    val sm: State[Mem,Val] = e match
      // EvalVal
      case v: Val => State insert v

      // EvalPrint
      case Print(e) => 
        for
          v <- eval(e)
        yield
          println(v.prettyVal) 
          Undefined

      // EvalUMinus  
      case UnOp(UMinus, e1) =>
        for
          n1 <- eToNum(e1)
        yield Num(- n1)

      // EvalNot  
      case UnOp(Not, e1) =>
        for
          b <- eToBool(e1)
        yield Bool(! b)

      // EvalDerefVar  
      case UnOp(Deref, a: Addr) =>
        for v <- readVal(a) yield v
      
      // EvalDerefFld
      case UnOp(FldDeref(f), e1) =>
        for
          a <- eToAddr(e1)
          fs <- readObj(a)
        yield fs getOrElse(f, throw StuckError(e))

      // EvalPlusNum, EvalPlusStr  
      case BinOp(Plus, e1, e2) =>
        for
          v1 <- eval(e1)
          v2 <- eval(e2)
        yield (v1, v2) match
          case (Str(s1), v2) => Str(s1 + toStr(v2))
          case (v1, Str(s2)) => Str(toStr(v1) + s2)
          case (v1, v2) => Num(toNum(v1) + toNum(v2))

      // EvalArith  
      case BinOp(bop@(Minus|Times|Div), e1, e2) =>
        for
          n1 <- eToNum(e1) 
          n2 <- eToNum(e2)
        yield (bop: @unchecked) match
          case Minus => Num(n1 - n2)
          case Times => Num(n1 * n2)
          case Div => Num(n1 / n2)

      // EvalAndTrue, EvalAndFalse  
      case BinOp(And, e1, e2) => 
        for
          b <- eToBool(e1)
          v <- if b then eval(e2) else State.insert[Mem,Val](Bool(b))
        yield v

      // EvalOrTrue, EvalOrFalse
      case BinOp(Or, e1, e2) =>
        for
          b <- eToBool(e1)
          v <- if b then State.insert[Mem,Val](Bool(b)) else eval(e2)
        yield v

      // EvalSeq  
      case BinOp(Seq, e1, e2) => 
        for
          _ <- eval(e1)
          v2 <- eval(e2)
        yield v2

      // EvalAssignVar  
      case BinOp(Assign, UnOp(Deref, a: Addr), e2) =>
        for
          v2 <- eval(e2)
          _ <- State.write { (m: Mem) => m + (a -> v2) }
        yield v2
      
      // EvalAssignFld 
      case BinOp(Assign, UnOp(FldDeref(f), e1), e2) =>
        for
          v2 <- eval(e2)
          a  <- eToAddr(e1)
          o <- readObj(a)
          _ = if !o.contains(f) then throw StuckError(e1)
          _  <- State.write { (m: Mem) => m + (a -> Obj(o + (f -> v2)).setPos(a.pos)) }
        yield v2

      // EvalEqual, EvalInequal*  
      case BinOp(bop@(Eq|Ne|Lt|Gt|Le|Ge), e1, e2) =>
        for
          v1 <- eval(e1)
          v2 <- eval(e2)
        yield (bop: @unchecked) match
          case Eq => Bool(v1 == v2)
          case Ne => Bool(v1 != v2)
          case Le|Ge|Lt|Gt => Bool(inequalityVal(bop, v1, v2))

      // EvalIfThen, EvalIfElse  
      case If(e1, e2, e3) => 
        for
          b <- eToBool(e1)
          v <- if b then eval(e2) else eval(e3)
        yield v

      // EvalConstDecl
      case Decl(MConst, x, ed, eb) =>
        for 
          vd <- eval(ed)
          v <- eval(subst(eb, x, vd))
        yield v

      // EvalLetDecl
      case Decl(MLet, x, ed, eb) =>
        for
          vd <- eval(ed)
          a <- Mem.alloc(vd)
          v <- eval(subst(eb, x, UnOp(Deref, a)))
        yield v
        
      // EvalCall
      case Call(Function(None, Nil, _, eb), Nil) =>
        eval(eb)
        
      // EvalCallConst
      case Call(v0@Function(None, (x1, _) :: xs, _, eb), e1 :: es) =>
        for
          v1 <- eval(e1)
          v <- eval(Call(v0.copy(xs=xs, e=subst(eb, x1, v1)).setPos(v0.pos), es).setPos(e.pos))
        yield v
      
      // EvalCallRec
      case Call(e0, es) =>
        for
          v0 <- eval(e0)
          v <- v0 match
            case v0@Function(Some(x0), _, _, eb) =>
              val v0p = v0.copy(p=None, e=subst(eb, x0, v0)).setPos(v0.pos)
              eval(Call(v0p, es).setPos(e.pos))
            case _ => 
              eval(Call(v0, es).setPos(e.pos))
        yield v
        
      // EvalObjLit
      case ObjLit(fes) =>
        val sm0 = State.insert[Mem,Map[Fld,Val]](Map.empty)
        fes.foldLeft(sm0):
          case (sm, (fi, (_, ei))) =>
            for
              o <- sm
              vi <- eval(ei)
            yield o + (fi -> vi)
        .flatMap:
          o => 
            Mem.alloc(Obj(o).setPos(e.pos))
        
      case Var(_) | UnOp(Deref, _) | BinOp(_, _, _) => 
        throw StuckError(e) // this should never happen
    
    sm map {v => v.pos = e.pos; v}
   
  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def evaluate(e: Expr): Val = eval(e)(Mem.empty)._2
  
  def evaluate(s: String): Val = eval(parse.fromString(s))(Mem.empty)._2
    
  def inferType(s: String): Typ = typeInfer(Map.empty, parse.fromString(s))
     
  
  /* Interface to run your interpreter from the command line.  You can ignore the code below. */ 
  
  def processFile(file: java.io.File): Unit = 
    if debug then
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    
    val expr = handle(fail()):
      parse.fromFile(file)
      
    if debug then
      println("Parsed expression:")
      println(expr)
    
    handle(fail()):
      if config.typeCheck then typeInfer(Map.empty, expr)
    
    handle(()):
      val (_, v) = eval(expr)(Mem.empty)
      println(v.prettyVal)
