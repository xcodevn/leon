/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

object Annotations {
  class induct extends StaticAnnotation
  class axiomatize extends StaticAnnotation
  class main extends StaticAnnotation
  class lemma extends StaticAnnotation
  class depend(lemmas: String*) extends StaticAnnotation
  class simp extends StaticAnnotation
}
