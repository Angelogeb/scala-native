package scala.scalanative.runtime

import scala.scalanative.unsafe.{CSize, extern, name}

@extern
object Local {

  @name("scalanative_local_enter1")
  def enter_1stclass(): Unit = extern

  @name("scalanative_localalloc")
  def alloc(rawty: RawPtr, size: CSize): RawPtr = extern

  @name("scalanative_local_exit1")
  def exit_1stclass(): Unit = extern
}
