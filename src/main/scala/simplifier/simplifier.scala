package simplifier

import java.lang.Integer

import AST._


// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {



  def simplify(node: Node): Node = node match {
    case nodeList @ NodeList(list) => NodeList(simplifyList(list))
    case list @ ElemList(_)  => ElemList(simplifyList(list.list))
    case assignment@Assignment(left, right) => simplifyAssignment(left, right)
    case binExpr@BinExpr(op, left, right) => simplifyBinExpr(binExpr)
    case unary@Unary(_, _) => simplifyUnary(unary)
    case classDef@ClassDef(name, list, suite) => simplifyClassDef(classDef)
    case tuple @ Tuple(_) => simplifyTuple(tuple)
    case intNum @ IntNum(_) => intNum
    case floatNum @ FloatNum(_) => floatNum
    case fundef @ FunDef(_, _, _) => simplifyFundef(fundef)
    case funcall @ FunCall(_, _) => simplifyFuncall(funcall)
    case lambdadef @ LambdaDef(_, _) => simplifyLambda(lambdadef)
    case _ => node //NodeList(List(simplifyNode(node).orNull))//node

  }
  def simplifyAssignment(left: Node, right: Node): Node = {
    val _right = simplify(right)

    Assignment(left, _right)
  }

  def simplifyBinExpr(binExpr: BinExpr): Node = {
    val _left = simplify(binExpr.left)
    val _right = simplify(binExpr.right)
//    BinExpr(binExpr.op, _left, _right) match {
//      case binOp@BinExpr("-", IntNum(i), _) => binOp.right
//      case binOp@BinExpr("-", _, IntNum(i)) => binOp.left
//      case binOp@BinExpr("+", IntNum(i), _) => binOp.right
//      case binOp@BinExpr("+", _, IntNum(i)) => binOp.left
//      case binOp@BinExpr("*", IntNum(one), _) => binOp.right
//      case binOp@BinExpr("*", _, IntNum(one)) => binOp.left
//      case binOp@BinExpr("/", IntNum(one), _) => binOp.right
//      case binOp@BinExpr("/", _, IntNum(one)) => binOp.left
//      case binOp@BinExpr("**", num1, num2) =>
    binExpr.op match {
      case "*" => (_left, _right) match {
        case (IntNum(n), _) if n == 0 => IntNum(0)
        case (_, IntNum(n)) if n == 0 => IntNum(0)
        case (IntNum(n), r) if n == 1 => r
        case (l, IntNum(n)) if n == 1 => l
        case (IntNum(l), IntNum(r)) => IntNum(r * l)
        case (FloatNum(l), FloatNum(r)) => FloatNum(r * l)
        case _ => BinExpr(binExpr.op, _left, _right)
      }
      case "+" => (_left, _right) match {
        case (IntNum(n), r) if n == 0 => r
        case (l, IntNum(n)) if n == 0 => l
        case (l, Unary("-", r)) => simplify(BinExpr("-", l, r))
        case (Unary("-", l), r) => simplify(BinExpr("-", r, l))
        case (IntNum(l), IntNum(r)) => IntNum(r + l)
        case (FloatNum(l), FloatNum(r)) => FloatNum(r + l)
        case (Tuple(l), Tuple(r)) => Tuple(l ++ r)
        case (ElemList(l), ElemList(r)) => ElemList(l++r)
        case _ => BinExpr(binExpr.op, _left, _right)
      }
      case "-" =>(_left, _right) match {
        case (IntNum(n), r) if n == 0 => r
        case (l, IntNum(n)) if n == 0 => l

        case (IntNum(l), IntNum(r)) => IntNum(r - l)
        case (FloatNum(l), FloatNum(r)) => FloatNum(r - l)
        case (l, r) if l == r => IntNum(0)
        case _ => BinExpr(binExpr.op, _left, _right)
      }
      case "/" => (_left, _right) match {
        case (IntNum(n), _) if n == 0 => IntNum(0)
        case (IntNum(n), r) if n == 1 => r
        case(l , r) if l == r => IntNum(1)
        //case (l, IntNum(n)) if n == 1 => l
        case (IntNum(l), IntNum(r)) => FloatNum(r / l)
        case _ => BinExpr(binExpr.op, _left, _right)

      }
      case "**" => (_left, _right) match {
        case (_, IntNum(k)) if k == 0 => IntNum(1)
        case (l, IntNum(k)) if k == 1 => l
        case _ => BinExpr(binExpr.op, _left, _right)
      }
      case _ => BinExpr(binExpr.op, _left, _right)
    }
    //TODO: Inne reguly
    //      op == '-' and l == IntNum(0) => r
    //TODO: Wszystkie operatory
  }

  def simplifyNode (node: Node) : Option[Node] = Some(simplify(node))
  def simplifyList(list: List[Node]) = {
    list.flatMap(simplifyNode)
  }
  def simplifyTuple(tuple: Tuple) = Tuple(simplifyList(tuple.list))
  def simplifyClassDef(classDef: ClassDef) = classDef

  def simplifyFundef(fundef: FunDef): Node = {
    FunDef(fundef.name, fundef.formal_args, simplify(fundef.body))
  }
  def simplifyFuncall(funcall: FunCall): Node = {
    FunCall(funcall.name, simplify(funcall.args_list))
  }
  def simplifyLambda(lambdadef: LambdaDef): Node = {
    LambdaDef(lambdadef.formal_args, simplify(lambdadef.body))
  }

  def simplifyUnary(unary: Unary) = {
    val ex = simplify(unary.expr)
    unary.op match{
      case "-" => ex match {
        case IntNum(n) => IntNum(-n)
        case FloatNum(n) => FloatNum(-n)
        case _ => Unary(unary.op,ex)
      }
      case "+" => ex
      case "not" => ex match{
        case TrueConst() => FalseConst()
        case FalseConst() => TrueConst()
        case _ => Unary(unary.op, ex)
      }
      case _ => Unary(unary.op, ex)
    }
  }
}
