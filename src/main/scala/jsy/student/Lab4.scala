package jsy.student

import jsy.lab4.Lab4Like
import sun.misc.FloatingDecimal.BinaryToASCIIConverter

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Anthony Tracy>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil => Nil
    case h1 :: Nil => h1 :: Nil
    case h1 :: (t1 @ (h2 :: _)) => if(h1!=h2) h1 :: compressRec(t1) else compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => if(acc.isEmpty || acc.head != h) h :: acc else acc
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case None => h :: mapFirst(t)(f)
      case Some(i) => i :: t
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc                                // we are at a leaf, return the data in the parent node
      case Node(l, d, r) => loop(f(loop(acc,l),d),r)   // We still have left's to fold through, and act the function on each inner loop
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){    // Passing in tuple () so the acc in this should be the same, while the head would be the next value
      (acc,h) => acc match {
        case (false,_) => (false,Some(h))
        case (true,None) => (true,Some(h))
        case (true, Some(d)) => if (d<h) (true,Some(h)) else (false,Some(h))
      }
    }
    b
  }
  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber                // By this point in code we can just return the type
      case B(_) => TBool                  // Same as above
      case Undefined => TUndefined        // Same as above
      case S(_) => TString                // " ... "
      case Var(x) => lookup(env,x)
      case Decl(mode, x, e1, e2) =>  (typeof(env,e1),typeof(extend(env,x,typeof(env,e1)),e2)) match {  // Match on the tp1 and typ2, but make sure to update enviroment for e2 with e1's type
        case (_,typ2) => typ2
      }
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env,e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (TNumber,TNumber) => TNumber                 // Addition can be done with only numbers      - TypePlusArith
        case (TString,TString) => TString                 // Concatonation can only be done with strings - TypePlusString
        case (tgot,_) => err(tgot,e1)//throw StaticTypeError(tgot,e1,e) // If e1 is anything else
        case (_,tgot) => err(tgot,e2)//throw StaticTypeError(tgot,e2,e) // If e2 is ANything else
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (TNumber,TNumber) => TNumber
        case (tgot,_) => err(tgot,e1)//throw StaticTypeError(tgot,e1,e)
        case (_,tgot) => err(tgot,e2)//throw StaticTypeError(tgot,e2,e)
      }
      // This looks sloppy ... I need to test it <----------------------------------------------------------------------
      // Also note that I am not sure if Undefined should pass through this, currently i think it does
      case Binary(Eq|Ne, e1, e2) => {
        val (typ1, typ2) = (typeof(env, e1), typeof(env, e2))           // Saving these since I need them more than once
        val (fun1, fun2) = (hasFunctionTyp(typ1), hasFunctionTyp(typ2)) // Saving these since I need them more than once
        if ((typ1 == typ2) && (!fun1 && !fun2)) TBool                   // Make sure we have no function type && e1,e2 have same type
        else {
          (fun1, fun2) match {                                          // Otherwise we will have an error to throw
            case (true, _) => err(typeof(env, e1),e1)//throw StaticTypeError(typeof(env, e1), e1, e)
            case (_, true) => err(typeof(env, e1),e2)//throw StaticTypeError(typeof(env, e2), e2, e)
          }
        }
      }

      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (TNumber,TNumber) => TBool                   // Only number should be compared to other nuumbers  - TypeInequalityyNumber
        case (TString,TString) => TBool                   // Only strings to strings                           - TypeInequalityString
        case (tgot,_) => err(tgot,e1)//throw StaticTypeError(tgot,e1,e)
        case (_,tgot) => err(tgot,e2)//throw StaticTypeError(tgot,e2,e)
      }
      case Binary(And|Or, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (TBool, TBool) => TBool                  // TypeAndOrNumber
        case (tgot,_) => err(tgot,e1)//throw StaticTypeError(tgot,e1,e)
        case (_,tgot) => err(tgot,e2)//throw StaticTypeError(tgot,e2,e)

      }
      case Binary(Seq, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
        case (_,typ2) => typ2
        //case (,)
      }
      // Should this also allow undefined ? < --------------------------------------------------------------------------
      case If(e1, e2, e3) => {
        val (typ1,typ2,typ3) = (typeof(env,e1),typeof(env,e2),typeof(env,e3))
        if (typ2==typ3){
          if(typ1==TBool) typ2 else err(typ1,e1)  // Throw error since e1 != bool
        } else err(typ2,e2)                       // Throw error since e1.Type != e2.Type
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /** *** Add cases here *****/
          case (Some(name), Some(ann)) =>
            val t = TFunction(params, ann)
            extend(env, name,  t)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.

        // This needs to be done in every case that we didn't throw an error
        val env2 = params.foldLeft(env1) {
          case (acc, (str, MTyp(_,typ))) => extend(acc, str,typ)
        }
        // return type of e1

        // Infer the type of the function body

        tann match {
          case None => TFunction(params, typeof(env2, e1))
          case Some(ann) =>
            val tmp  = typeof(env2,e1)
            if(ann == tmp)
              TFunction(params, typeof(env2, e1))
            else
              err(typeof(env2,e1),e1)
        }

        // Check with the possibly annotated return type
      }

      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {  // (('str',MTyp(mode,type)),args)
            case ((_,MTyp(_,typ)),arg) => if (typeof(env,arg) != typ) err(typeof(env,arg),arg)
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map( {case (str,exp) => (str,typeof(env,exp))}))
      case GetField(e1, f) => typeof(env,e1) match {
        case TObj(fields) => fields.get(f) match {
          case Some(typ) => typ
          case None => err(typeof(env,e1),e1)
        }
        case tgot => err(tgot,e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => {
        bop match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 <= s2
          //case _ => ??? // delete this line when done
        }
      }
      case (N(n1), N(n2)) => {
        bop match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 <= n2
          //case _ => ??? // delete this line when done
        }
      }
      case (e1,_) => throw StuckError(e1)
      case (_,e2) => throw StuckError(e2)
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(part_e) => loop(part_e,n+1)
      case _ => throw StuckError(e)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop,substitute(e1,esub,x))
      case Binary(bop, e1, e2) => Binary(bop,substitute(e1,esub,x),substitute(e2,esub,x))
      case If(e1, e2, e3) => If(substitute(e1,esub,x),substitute(e2,esub,x),substitute(e3,esub,x))
      case Var(y) => if(y==x) esub else e
      case Decl(mode, y, e1, e2) => if(y!=x) Decl(mode,y,substitute(e1,esub,x),substitute(e2,esub,x)) else Decl(mode,y,substitute(e1,esub,x),e2)
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        case None
      }
      case Call(e1, args) => ???
        /***** New cases for Lab 4 */
      case Obj(fields) => ???
      case GetField(e1, f) => ???
    }

    val fvs = freeVars(???)
    def fresh(x: String): String = if (???) fresh(x + "$") else x
    subst(???)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => ???
        case Binary(bop, e1, e2) => ???
        case If(e1, e2, e3) => ???

        case Var(y) =>
          ???
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          ???

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => ???
            case Some(x) => ???
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            ???
          }
          ???
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => ???
    case MName => ???
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(n)) if isValue(N(n)) => N(-n)
      case Unary(Not,B(b)) => B(!b)


      case Binary(bop,e1,e2) => bop match {
        // Sequence
        case Seq => step(e1); step(e2)
        // Artitmetic and String  concatination
        case Plus => (e1, e2) match {
          case (S(s1), S(s2)) => S(s1 + s2)
          case (N(n1), N(n2)) => N(n1 + n2)
        }
        case Minus => (e1, e2) match {
          case (N(n1), N(n2)) => N(n1 - n2)
        }
        case Times => (e1, e2) match {
          case (N(n1), N(n2)) => N(n1 * n2)
        }
        case Div => (e1, e2) match {
          case (N(n1), N(n2)) => N(n1 / n2) // Nevermind devide by zero in scala returns inf ...else Undefined
        }
        // Inequalities

      }




        /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (???) {
              val e1p = pazip.foldRight(e1) {
                ???
              }
              p match {
                case None => ???
                case Some(x1) => ???
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                ???
              }
              ???
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => ???
        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) => ???
      case Call(e1, args) => ???
        /***** New cases for Lab 4. */

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

