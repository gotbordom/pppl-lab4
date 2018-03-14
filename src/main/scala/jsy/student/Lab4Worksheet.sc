/*
 * CSCI 3155: Lab 4 Worksheet
 *
 * This worksheet demonstrates how you could experiment
 * interactively with your implementations in Lab4.scala.
 */

// Imports the parse function from jsy.lab1.Parser
import jsy.lab4.Parser.parse

// Imports the ast nodes
import jsy.lab4.ast._

// Imports all of the functions form jsy.student.Lab2 (your implementations in Lab2.scala)
import jsy.student.Lab4._

// Try compressRec
//val cr1 = compressRec(List(1, 2, 2, 3, 3, 3))

// Parse functions with possibly multiple parameters and type annotations.
parse("function fst(x: number, y: number): number { return x }")
parse("function (x: number) { return x }")
parse("function (f: (y: number) => number, x: number) { return f(x) }")

// Parse objects
parse("{ f: 0, g: true }")
parse("x.f")


def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
  def loop(acc: A, t: Tree): A = t match {
    case Empty => acc                                // we are at a leaf, return the data in the parent node
    case Node(l, d, r) => loop(f(loop(acc,l),d),r)   // We still have left's to fold through, and act the function on each inner loop
  }
  loop(z, t)
}



def strictlyOrdered(t: Tree): Boolean = {
  val (b, _) = foldLeft(t)((true, None: Option[Int])){    // Passing in tuple () so the acc in this should be the same, while the head would be the next value
    // Case 1: Do we already have a false result? if so just pass the false through
    case ((false,_),h) => (false,Some(h))
    // case 2: what is the base case? - when the data of the node we are at is nil and thus must be lower than anyting else
    case ((true,None),_) => (true,None)
    // case 3: we have a true and need to know if we are still true
    case ((true,Some(d)),h) => if(d < h) (true,Some(h)) else (false,Some(h))
    //case _ => {
      println("Something is wrong.\n")
      (true,Some(1))
    }
  }
  b
}



// Some test cases:
// NOTE: t* are actual BSTs
//       f* are false BSTs
val t1 = Node(Empty,1,Empty)                  // Balances base case of tree
val t1_1 = Node(Empty,6,Empty)                   // Let t1_() be leafs...
val t2 = Node(t1,2,Node(Empty,3,Empty))       // Balances easy depth 1 case of tree
val t3 = Node(t2,4,Node(Empty,5,t1_1))       // Making lots of these
val f1 = Node(t3,6,Empty)                    // Testing that the tree should only be BST without repeats
val f2 = Node(t3,7,t1)                       // Testing that the BST Should actually be a BST


val testTrue_1 = strictlyOrdered(t1)
val testTrue_2 = strictlyOrdered(t2)
val testTrue_3 = strictlyOrdered(t3)
val testFalse_1 = strictlyOrdered(f1)
val testFalse_2 = strictlyOrdered(f2)
