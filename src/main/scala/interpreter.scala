

trait Env {

  type ValueMap = Map[String, ValueDeclBody]
  type TypeMap  = Map[String, TypeDeclBody]

  val body : Map[String, (ValueMap, TypeMap)]

  def +(x : String, decls : List[Declaration]) = {
    val mapPair : (ValueMap, TypeMap) = {
      val init : (ValueMap, TypeMap) = (Map(), Map());
      decls.foldLeft(init){ case ((valmap, tymap), decl) =>
        decl match {
          case DeclForValueLabel(vl, vd) => (valmap + ((vl, vd)), tymap)
          case DeclForTypeLabel(tl, td)  => (valmap, tymap + ((tl, td)))
        }
      }
    };
    new Env { val body = Env.this.body + ((x, mapPair)) }
  }


  def findDeclVal(x : String, vlabel : String) : Option[(Type, Option[Ast])] =
    body.get(x) match {
      case None =>
        None

      case Some((valmap, _)) =>
        valmap.get(vlabel) match {
          case Some(DeclVal(ty, astopt)) => Some((ty, astopt))
          case _                         => None
        }
    }

}

class EmptyEnv extends Env {
  val body : Map[String, (ValueMap, TypeMap)] = Map()
}


sealed abstract class EvalError
case class NotImplementedYet(msg : String)       extends EvalError
case class ValueLabelNotFound(vl : String)       extends EvalError
case class ValueLabelNotImplemented(vl : String) extends EvalError


class FWSInterpreter {

  def run(ast : Ast) = {
    val env = new EmptyEnv;
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
            env.findDeclVal(x, vlabel) match {
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
