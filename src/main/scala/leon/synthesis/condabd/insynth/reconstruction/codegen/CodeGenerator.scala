package leon
package synthesis.condabd.insynth
package reconstruction.codegen

import scala.text.Document
import scala.text.Document.empty

import leon._
import insynth.reconstruction.stream._
import insynth.structures.Function
import insynth.util.logging.HasLogger

import purescala.Trees.{ Expr }
import purescala.TypeTrees.{ TypeTree => DomainType, FunctionType }
import purescala.{ TypeTrees => domain }
import purescala.Trees.{ Expr => CodeGenOutput }

/**
 * class that converts an intermediate tree into a list of output elements (elements
 * capable of Scala code generation)
 * should be extended to provide syntax-style variants
 */
class CodeGenerator extends (Node => CodeGenOutput) with HasLogger {

  /**
   * takes the tree and calls the recursive function and maps documents to Output elements
   * @param tree root of intermediate (sub)tree to transform
   * @return list of output (code snippet) elements
   */
  def apply(tree: Node) = {
    // match the starting tree to an application that produces query type
    tree match {
      case Application(Function(_, _ /* BottomType */), queryDec :: List(innerApp)) =>
      	transform(innerApp)
      case _ => throw new RuntimeException
    }
  }
  
  /** transform context determines the place of the element to transform */
  object TransformContext extends Enumeration {
    type TransformContext = Value
    // expression, application, parameter, argument (in a function), single parameter
    val Expr, App, Par, Arg, SinglePar = Value
  }
  // import all transform context values
  import TransformContext._
  
  /**
   * main method (recursive) for transforming a intermediate (sub)tree
   * @param tree root node of the (sub)tree to transform 
   * @return list of documents containing all combinations of available expression for
   * the given (sub)tree
   */
  def transform(tree: Node): CodeGenOutput = {    
    tree match {
      // variable (declared previously as arguments)
      case Variable(tpe, name) =>
        // what to do here
        throw new RuntimeException
      // identifier from the scope
      case Identifier(tpe, LeonDeclaration(_, _, _, im: ImmediateExpression)) => 
        im()
      // apply parameters in the tail of params according to the head of params 
      case app@Application(tpe, params) => {        
        // match the application definition term
        params.head match {
          case Identifier(_, decl: LeonDeclaration)  => {            
	          info("Generating application: " + decl + " with params: " + params + " params.size = " + params.size)   

	          // for an expression of each parameters yield the appropriate transformed expression	            
            val paramsExpr: List[CodeGenOutput] = params.tail.map(transform _)
	               
            decl.expression match {
              // identifier is a function
              case NaryReconstructionExpression(_, fun) =>  
		            info("NaryReconstructionExpression with params: " + paramsExpr + " paramsExpr.size = " + paramsExpr.size)  
                assert(paramsExpr.size >= 1)             
                
                // return application of transformed parameters to fun
                fun(paramsExpr)
                
              // identifier is an immediate expression
              case ImmediateExpression(_, expr) =>
                assert(paramsExpr.isEmpty)
                expr
                
              // identifier is an unary operator
              case UnaryReconstructionExpression(_, fun) =>
                assert(paramsExpr.size == 1)
                fun(paramsExpr.head)
                
              // this should not happen
              case _ => throw new Exception("Unsupported reconstruction: " + decl.expression)
            }
          } // case Identifier
          
          case innerApp@Application(appType: Function, params) =>
            warning("Cannot have app head: " + innerApp + " in application " + app)
          	throw new Exception("Cannot have app head: " + innerApp + " in application " + app)
                      
          // function that is created as an argument or anything else
          case /*Identifier(_, _:AbsDeclaration) | */_:Variable | _ =>
          	throw new Exception("Unsupported combination for application head " + params.head)
          	
        } // params.head match 
      }
      
      // abstraction first creates all of its arguments
      case Abstraction(tpe, vars, subtrees) =>
        assert(vars.size > 0)        
        throw new RuntimeException
        
    } // tree match
  }
  
}