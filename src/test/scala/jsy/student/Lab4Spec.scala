package jsy.student

import jsy.lab4.Lab4Like
import jsy.lab4.ast._
import jsy.tester.JavascriptyTester
import org.scalatest._

class Lab4Spec(lab4: Lab4Like) extends FlatSpec {
  import lab4._

  /***** Higher-Function Exercises Tests *****/

  "compressRec/compressFold" should "compress List(1, 2, 2, 3, 3, 3)" in {
    val l1 = List(1, 2, 2, 3, 3, 3)
    val gold1 = List(1, 2, 3)
    assertResult(gold1) { compressRec(l1) }
    assertResult(gold1) { compressFold(l1) }
  } 
  
  "mapFirst" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     assertResult(gold1) {
       mapFirst(l1) { (i: Int) => if (i < 0) Some(-i) else None }
     }
  }
  
  "foldLeft" should "enable implementing treeFromList and sum" in {
    assertResult(6){
      sum(treeFromList(List(1, 2, 3)))
    }
  }

  "strictlyOrdered" should "check strict ordering of a binary search tree" in {
    assert(!strictlyOrdered(treeFromList(List(1,1,2))))
    assert(strictlyOrdered(treeFromList(List(1,2))))
  }


  /***** Interpreter Tests *****/

  {
    /* Unary cases */
    // Test values to use
    val xtype = TNumber
    val baseS = TString
    val baseB = TBool
    val baseU = TUndefined

    val THIS = S("this")
    val THAT = S("that")

    val TRUE = B(true)
    val FALSE = B(false)

    // Negative base cases
    val neg0 = Unary(Neg,N(1))
    val neg1 = Unary(Neg,N(1))
    val neg2 = Unary(Neg,N(-1))
    val neg3 = Unary(Neg,neg2)

    // These should fail
    val neg4 = Unary(Neg,B(true))
    val neg5 = Unary(Neg,B(false))
    val neg6 = Unary(Neg,S("test"))
    val neg7 = Unary(Neg,Undefined)


    // ! base cases
    //these should fail
    val not0 = Unary(Not,N(0))
    val not1 = Unary(Not,N(1))
    val not2 = Unary(Not,N(-1))
    val not3 = Unary(Not,not2)

    // These should pass
    val not4 = Unary(Not,B(true))
    val not5 = Unary(Not,B(false))
    val not6 = Unary(Not,S("test"))
    val not7 = Unary(Not,Undefined)

    // Extend a map with xTypes
    val tenvx = extend(empty, "x", xtype)  // Var of number
    val tenvS = extend(empty, "x", baseS)  // Var of str
    val tenvB = extend(empty, "x", baseB)  // Var to bool
    val tenvU = extend(empty, "x", baseU)  // Var of undefined

    // TypeVar testing
    "TypeVar" should "perform TypeVar" in {
      assertResult(xtype) {
        typeof(tenvx, Var("x"))
      }
      assertResult(baseS) {
        typeof(tenvS, Var("x"))
      }
      assertResult(baseB) {
        typeof(tenvB, Var("x"))
      }
      assertResult(baseU) {
        typeof(tenvU, Var("x"))
      }
    }

    // Probably want to write some more tests for typeInfer, substitute, and step.
    "TypeNeg" should "perform TypeNeg" in {
      // Return number
      assertResult(xtype){
        typeof(empty, neg0)
      }
      assertResult(xtype){
        typeof(empty, neg1)
      }
      assertResult(xtype){
        typeof(empty, neg2)
      }
      assertResult(xtype){
        typeof(empty, neg3)
      }
      //Returns errors

      /*
      // throw StaticTypeError(tgot, e1, e)
      typeof(empty,neg5)
      typeof(empty,neg6)
      typeof(empty,neg7)
      */
    }

    "TypeNot" should "perfrom TypeNot" in {
      // Returns bool:
      assertResult(baseB){
        typeof(empty, not4)
      }
      assertResult(baseB){
        typeof(empty, not5)
      }
      /*
      assertResult(baseB){
        typeof(empty, not2)
      }
      assertResult(baseB){
        typeof(empty, not3)
      }
      */
    }


    /* Binary cases */

    val seq0 = Binary(Seq,not4,neg1) // Should return a num even with bool and num
    val seq1 = Binary(Seq,neg1,not4) // Should return opposite


    "TypeSeq" should "perform TypeSeq" in {
      assertResult(xtype){
        typeof(empty,seq0)
      }
      assertResult(baseB){
        typeof(empty,seq1)
      }
    }

    val plus0 = Binary(Plus,neg0,neg1)   // Should return num + num => num
    val minus0 = Binary(Minus,neg0,neg1) // Again num - num => num
    val div0 = Binary(Div,neg0,neg1)     // num / num => num
    val times0 = Binary(Times,neg0,neg1) // num * num => 0

    val cat0 = Binary(Plus,S("Test"),S("This"))    // str+str => str

    "TypeArith and TypePlusStr" should "perform Type Arith and PlusStr" in {
      assertResult(xtype){
        typeof(empty,plus0)
      }
      assertResult(xtype){
        typeof(empty,minus0)
      }
      assertResult(xtype){
        typeof(empty,div0)
      }
      assertResult(xtype){
        typeof(empty,times0)
      }
      assertResult(baseS){
        typeof(empty,cat0)
      }
    }



    val leNum0 = Binary(Le,neg0,neg1)  // num <= num => bool
    val leStr0 = Binary(Le,THIS,THAT)  // str <= str => bool

    val geNum0 = Binary(Ge,neg0,neg1)  // num >= num => bool
    val geStr0 = Binary(Ge,THIS,THAT)  // str <= str => bool

    val ltNum0 = Binary(Lt,neg0,neg1)  // num < num => bool
    val ltStr0 = Binary(Lt,THIS,THAT)  // str < str => bool

    val gtNum0 = Binary(Gt,neg0,neg1)  // num < num => bool
    val gtStr0 = Binary(Gt,THIS,THAT)  // str < str => bool


    "TypeInequality - Str and Num" should "perform TypeInequality" in {
      // Number inputs
      assertResult(baseB){
        typeof(empty,leNum0)
      }
      assertResult(baseB){
        typeof(empty,ltNum0)
      }
      assertResult(baseB){
        typeof(empty,gtNum0)
      }
      assertResult(baseB){
        typeof(empty,geNum0)
      }
      // String inputs
      assertResult(baseB){
        typeof(empty,leNum0)
      }
      assertResult(baseB){
        typeof(empty,ltNum0)
      }
      assertResult(baseB){
        typeof(empty,gtNum0)
      }
      assertResult(baseB){
        typeof(empty,geNum0)
      }
    }


    val eqNum0 = Binary(Eq,neg0,neg1)
    val eqStr0 = Binary(Eq,THIS,THAT)
    val eqBool0 = Binary(Eq,TRUE,FALSE)
    val eqUndef = Binary(Eq,Undefined,Undefined)

    val neNum0 = Binary(Ne,neg0,neg1)
    val neStr0 = Binary(Ne,THIS,THAT)
    val neBool0 = Binary(Ne,TRUE,FALSE)
    val neUndef = Binary(Ne,Undefined,Undefined)

    "TypeEquality - no function types" should "perform TypeEquality" in {

      // Equality
      assertResult(baseB){
        typeof(empty,eqNum0)
      }
      assertResult(baseB){
        typeof(empty,eqStr0)
      }
      assertResult(baseB){
        typeof(empty,eqBool0)
      }
      assertResult(baseB){
        typeof(empty,eqUndef)
      }

      // Non-Equality
      assertResult(baseB){
        typeof(empty,neNum0)
      }
      assertResult(baseB){
        typeof(empty,neStr0)
      }
      assertResult(baseB){
        typeof(empty,neBool0)
      }
      assertResult(baseB){
        typeof(empty,neUndef)
      }

    }

    val and0 = Binary(And,eqNum0,eqStr0)
    val or0 = Binary(Or, eqNum0,eqStr0)
    "TypeAndOr" should "perform AndOr" in {
      // And

      assertResult(baseB){
        typeof(empty,and0)
      }
      // Or
      assertResult(baseB){
        typeof(empty,or0)
      }
    }

    val if0 = If(and0,neg0,neg1)      // Testing return num
    val if1 = If(or0,THIS,THAT)       // Testing return string
    val if2 = If(eqNum0,TRUE, FALSE)  // Testing return bool
    val if3 = If(neNum0,Undefined,Undefined) // Testing undefined case

    "TypeIf" should "perfrom If - IF it works..." in {
      assertResult(xtype){
        typeof(empty, if0)
      }
      assertResult(baseS){
        typeof(empty, if1)
      }
      assertResult(baseB){
        typeof(empty, if2)
      }
      assertResult(baseU){
        typeof(empty, if3)
      }
    }



    //Decl(mode, x, e1, e2)

    val decl0 = Decl(MConst, "x",plus0,Var("x")) // Decl x = num + num => num
    val decl1 = Decl(MConst, "x",cat0,Var("x"))  // Decl x = str+str => num
    val decl2 = Decl(MConst, "x",and0,Var("x"))  // Decl x = Some() And Some() => Bool
    val decl3 = Decl(MConst, "x",Undefined,Var("x")) // Decl x = Undefined => Undefined


    "TypeDecl" should "perform Decl" in {
      assertResult(xtype){
        typeof(empty,decl0)
      }
      assertResult(baseS){
        typeof(empty,decl1)
      }
      assertResult(baseB){
        typeof(empty,decl2)
      }
      assertResult(baseU){
        typeof(empty,decl3)
      }


     /*  Now to test the Step fucntions */
     //"DoNeg" should "perform step on neg" in {



     //}



    }

  }

}

// An adapter class to pass in your Lab4 object.
class Lab4SpecRunner extends Lab4Spec(jsy.student.Lab4)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab4.
// The test expects a corresponding .ans file with the expected result.
class Lab4JsyTests extends JavascriptyTester(None, "lab4", jsy.student.Lab4)

class Lab4Suite extends Suites(
  new Lab4SpecRunner,
  new Lab4JsyTests
)