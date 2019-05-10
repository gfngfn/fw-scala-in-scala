
class Env(_body : Map[String, List[Declaration]]) {

  val body : Map[String, List[Declaration]] = _body


  def +(x : String, decls : List[Declaration]) =
    new Env(this.body + ((x, decls)))


  def findDeclVar(vlabel : String) : Option[(Type, Option[Ast])] =
    None  // TEMPORARY

}
/*
object Env {
  def apply : Env = new Env(Map())
}
*/


sealed abstract class EvalError
case class NotImplementedYet(msg : String)       extends EvalError
case class ValueLabelNotFound(vl : String)       extends EvalError
case class ValueLabelNotImplemented(vl : String) extends EvalError


class FWSInterpreter {

  def run(ast : Ast) = {
    val env = new Env(Map());
    interpret(env, ast)
  }

  def interpret(env : Env, ast : Ast) : Either[EvalError, Value] =
    ast match {
      case ValNewIn(x, ty, ast0) =>
        val decls = lookupDeclarations(env, ty, x);
        interpret(env + (x, decls), ast0)

      case Var(x) =>
        Right(ValVar(x))

      case Access(ast0, vlabel) =>
        val res0 = interpret(env, ast0);
        res0 match {
          case Left(_) =>
            res0

          case Right(ValVar(x)) =>
            env.findDeclVar(vlabel) match {
              case None                     => Left(ValueLabelNotFound(vlabel))
              case Some((_, None))          => Left(ValueLabelNotImplemented(vlabel))
              case Some((ty, Some(astNew))) => interpret(env, astNew)
            }
        }

      case Call(ast0, vlabel, astargs) =>
        Left(NotImplementedYet("evaluation for method calls"))  // TEMPORARY
    }

  def lookupDeclarations(env : Env, ty : Type, x : String) =
    Nil  // TEMPORARY
}
