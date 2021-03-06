package java.lang

import java.nio.charset.{Charset, StandardCharsets}

import org.junit.Ignore
import org.junit.Test
import org.junit.Assert._

import scalanative.junit.utils.AssertThrows._

class StringTest {

  @Test def stringArrayByteIntIntStringWithNullEncoding(): Unit = {
    assertThrows(classOf[java.lang.NullPointerException],
                 new String("I don't like nulls".getBytes, 0, 3, null: String))
  }

  @Test def stringArrayByteIntIntStringWithUnsupportedEncoding(): Unit = {
    assertThrows(
      classOf[java.io.UnsupportedEncodingException],
      new String("Pacem in terris".getBytes, 0, 3, "unsupported encoding"))
  }

  @Test def stringArrayByteStringWithNullEncoding(): Unit = {
    assertThrows(classOf[java.lang.NullPointerException],
                 new String("Nulls are just as bad".getBytes, null: String))
  }

  @Test def stringArrayByteStringWithUnsupportedEncoding(): Unit = {
    assertThrows(
      classOf[java.io.UnsupportedEncodingException],
      new String("to people of goodwill.".getBytes, "unsupported encoding"))
  }

  @Test def stringArrayByteStartLengthWithInvalidStartOrLength(): Unit = {
    val chars: Array[Char] = Array('a', 'b', 'c')

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 new String(chars, -1, chars.length) // invalid start
    )

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 new String(chars, 0, chars.length + 1) // invalid length
    )
  }

  @Test def stringArrayIntOffsetCountWithInvalidOffsetOrCount(): Unit = {
    val codePoints = Array[Int](235, 872, 700, 298)

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 new String(codePoints, -1, codePoints.length) // invalid offset
    )

    assertThrows(
      classOf[java.lang.StringIndexOutOfBoundsException],
      new String(codePoints, 0, codePoints.length + 1) // invalid length
    )
  }

  @Test def plus(): Unit = {
    assertTrue("big 5" == "big " + 5.toByte)
    assertTrue("big 5" == "big " + 5.toShort)
    assertTrue("big 5" == "big " + 5)
    assertTrue("big 5" == "big " + 5L)
    assertTrue("5 big" == 5.toByte + " big")
    assertTrue("5 big" == 5.toShort + " big")
    assertTrue("5 big" == 5 + " big")
    assertTrue("5 big" == 5L + " big")
    assertTrue("foo" == "foo" + "")
    assertTrue("foo" == "" + "foo")
    assertTrue("foobar" == "foo" + "bar")
    assertTrue("foobarbaz" == "foo" + "bar" + "baz")
  }

  @Test def codePointAtIndexWithInvalidIndex(): Unit = {
    val data = "When in the Course"

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 data.codePointAt(-1))

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 data.codePointAt(data.length + 1))
  }

  @Test def codePointBeforeIndexWithInvalidIndex(): Unit = {
    val data = "of human events"

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 data.codePointBefore(-1))

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 // Careful here, +1 is valid +2 is not
                 data.codePointBefore(data.length + 2))
  }

  @Test def codePointCountBeginIndexEndIndexWithInvalidBeginOrEndIndex()
      : Unit = {
    val data = "it becomes necessary"

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 data.codePointCount(-1, data.length))

    assertThrows(classOf[java.lang.StringIndexOutOfBoundsException],
                 data.codePointCount(0, data.length + 1))
  }

  @Test def compareTo(): Unit = {
    assertTrue("test".compareTo("utest") < 0)
    assertTrue("test".compareTo("test") == 0)
    assertTrue("test".compareTo("stest") > 0)
    assertTrue("test".compareTo("tess") > 0)
  }

  @Test def compareToIgnoreCase(): Unit = {
    assertTrue("test".compareToIgnoreCase("Utest") < 0)
    assertTrue("test".compareToIgnoreCase("Test") == 0)
    assertTrue("Test".compareToIgnoreCase("stest") > 0)
    assertTrue("tesT".compareToIgnoreCase("teSs") > 0)
  }

  @Test def equalsIgnoreCase(): Unit = {
    assertTrue("test".equalsIgnoreCase("TEST"))
    assertTrue("TEst".equalsIgnoreCase("teST"))
    assertTrue(!("SEst".equalsIgnoreCase("TEss")))
  }

  @Test def regionMatches(): Unit = {
    assertTrue("This is a test".regionMatches(10, "test", 0, 4))
    assertTrue(!("This is a test".regionMatches(10, "TEST", 0, 4)))
    assertTrue("This is a test".regionMatches(0, "This", 0, 4))
  }

  @Test def replaceChar(): Unit = {
    assertTrue("test".replace('t', 'p') equals "pesp")
    assertTrue("Test".replace('t', 'p') equals "Tesp")
    assertTrue("Test".replace('T', 'p') equals "pest")
    assertTrue("Test".replace('0', '1') equals "Test")
  }

  @Test def replaceCharSequence(): Unit = {
    // Runs assertion with and without prefix and suffix
    def check(input: String, replace: String => Boolean) = {
      assertTrue(replace(input))

      val inputWithPrefix = ("[" + input).substring(1)
      assertTrue(inputWithPrefix equals input)
      assertTrue(replace(inputWithPrefix))

      val inputWithSuffix = (input + "]").substring(0, input.length)
      assertTrue(inputWithSuffix equals input)
      assertTrue(replace(inputWithSuffix))

      val inputWithBoth = ("[" + input + "]").substring(1, input.length + 1)
      assertTrue(inputWithBoth equals input)
      assertTrue(replace(inputWithBoth))
    }

    check("test", _.replace("t", "p") equals "pesp")
    check("Test", _.replace("t", "p") equals "Tesp")
    check("test", _.replace("e", "oa") equals "toast")
    check("Test", _.replace("T", "p") equals "pest")
    check("spantanplans", _.replace("an", ".") equals "sp.t.pl.s")
    check("spantanplans", _.replace("an", "") equals "sptpls")
    check("Test", _.replace("0", "1") equals "Test")
    check("Test", _.replace("e", "") equals "Tst")
    check("Test", _.replace("t", "") equals "Tes")
    check("Test", _.replace("", "") equals "Test")
    check("Test", _.replace("", "--") equals "--T--e--s--t--")
  }

  @Test def replaceAllNonAscii(): Unit = {
    val greetings = "Gruesze"

    val greetingsWithUmlaut = greetings.replaceAll("ue", "??")
    assertTrue(greetingsWithUmlaut == "Gr??sze")

    val greetingsWithUmlautAndSharpS = greetingsWithUmlaut.replaceAll("sz", "??")
    assertTrue(greetingsWithUmlautAndSharpS == "Gr????e")

    assertTrue(
      "Grueszszszeszszszszsze".replaceAll("sz", "??") == "Grue??????e??????????e")
  }

  @Test def replaceAllLiterallyWithDollarSignInReplacementIssue1070(): Unit = {
    val literal     = "{.0}"
    val replacement = "\\$ipsum"
    val prefix      = "Lorem "
    val suffix      = " dolor"
    val text        = prefix + literal + suffix
    val expected    = prefix + replacement + suffix

    assertTrue(text.replaceAllLiterally(literal, replacement) == expected)
  }

  private def splitVec(s: String, sep: String, limit: Int = 0) =
    s.split(sep, limit).toVector

  private def splitTest(sep: String, splitExpr: Option[String] = None) = {
    val splitSep = splitExpr getOrElse sep
    val n        = 4
    val limit    = 2

    assertTrue(splitVec("", splitSep) == Vector(""))
    assertTrue(splitVec("", splitSep, limit) == Vector(""))

    val noSep = "b"
    assertTrue(splitVec(noSep, splitSep) == Vector(noSep))
    assertTrue(splitVec(noSep, splitSep, limit) == Vector(noSep))

    (1 to n) foreach { i =>
      val allSep = sep * n
      assertTrue(splitVec(allSep, splitSep) == Vector.empty)
      assertTrue(
        splitVec(allSep, splitSep, n) == (0 until (n - 1))
          .map(_ => "")
          .toVector :+ sep)
      assertTrue(
        splitVec(allSep, splitSep, limit) == (0 until (limit - 1))
          .map(_ => "")
          .toVector :+ allSep.drop((limit - 1) * sep.length))
    }

    val oneSep = noSep + sep
    assertTrue(splitVec(oneSep, splitSep) == Vector(noSep))
    assertTrue(splitVec(oneSep, splitSep, 1) == Vector(oneSep))
    assertTrue(splitVec(oneSep, splitSep, 2) == Vector(noSep, ""))

    val twoSep = oneSep * 2
    assertTrue(splitVec(twoSep, splitSep) == Vector(noSep, noSep))
    assertTrue(splitVec(twoSep, splitSep, 1) == Vector(twoSep))
    assertTrue(splitVec(twoSep, splitSep, 2) == Vector(noSep, oneSep))
    assertTrue(splitVec(twoSep, splitSep, 3) == Vector(noSep, noSep, ""))

    val leadingSep = sep + noSep
    assertTrue(splitVec(leadingSep, splitSep) == Vector("", noSep))
    assertTrue(splitVec(leadingSep, splitSep, 1) == Vector(leadingSep))
    assertTrue(splitVec(leadingSep, splitSep, 2) == Vector("", noSep))
    assertTrue(splitVec(leadingSep, splitSep, 3) == Vector("", noSep))

    val trailingSep = noSep + sep
    assertTrue(splitVec(trailingSep, splitSep) == Vector(noSep))
    assertTrue(splitVec(trailingSep, splitSep, 1) == Vector(trailingSep))
    assertTrue(splitVec(trailingSep, splitSep, 2) == Vector(noSep, ""))
    assertTrue(splitVec(trailingSep, splitSep, 3) == Vector(noSep, ""))

    val leadingPlusTrailing = sep + noSep + sep
    assertTrue(splitVec(leadingPlusTrailing, splitSep) == Vector("", noSep))
    assertTrue(
      splitVec(leadingPlusTrailing, splitSep, 1) == Vector(leadingPlusTrailing))
    assertTrue(splitVec(leadingPlusTrailing, splitSep, 2) == Vector("", oneSep))
    assertTrue(
      splitVec(leadingPlusTrailing, splitSep, 3) == Vector("", noSep, ""))
    assertTrue(
      splitVec(leadingPlusTrailing, splitSep, 4) == Vector("", noSep, ""))
  }

  @Test def split(): Unit = {
    splitTest("a")
    splitTest(".", splitExpr = Some("\\."))
    splitTest("ab", splitExpr = Some("ab"))
    splitTest("ab", splitExpr = Some("(ab)"))
  }

  @Test def getBytes(): Unit = {
    val b = new Array[scala.Byte](4)
    // This form of getBytes() has been depricated since JDK 1.1
    "This is a test".getBytes(10, 14, b, 0)
    assertTrue(new String(b) equals "test")
  }

  def testEncoding(charset: String, expectedInts: Seq[Int]): Unit = {
    testEncoding(Charset.forName(charset), expectedInts)
  }

  def testEncoding(charset: Charset, expectedInts: Seq[Int]): Unit = {
    // Try to break getBytes, test with difficult characters.
    // \u00DF Greek lowercase beta; expect 2 output bytes
    // \u4E66 Han Character 'book, letter, document; writings' ; 3 output bytes
    // \u1F50A emoji 'speaker with three sound waves'; 4 output bytes.
    //
    // Reference: http://stn.audible.com/abcs-of-unicode/
    //		       // replace 4E66 with hex string of interest
    //		  http://www.fileformat.info/info/unicode/char/4E66/index.htm

    val text = "\u0000\t\nAZaz09@~\u00DF\u4E66\u1F50A"

    // sanity check on character escapes, missing backslash or 'u', etc.
    assertEquals(text.length, 15)

    val bytes         = text.getBytes(charset)
    val expectedBytes = expectedInts.map(i => java.lang.Byte.valueOf(i.toByte))
    val expected      = Array[java.lang.Byte](expectedBytes: _*)
    assertTrue("result != expected}", bytes.sameElements(expected))
  }

  @Test def getBytesUTF8(): Unit = {

    val expectedInts =
      Seq(0, 9, 10, 65, 90, 97, 122, 48, 57, 64, 126, // one byte unicode
        -61, -97,                                     // two byte unicode
        -28, -71, -90,                                // three byte unicode
        -31, -67, -112, 65                            // four byte unicode
        )

    testEncoding(StandardCharsets.UTF_8, expectedInts)
    testEncoding("UTF-8", expectedInts)
  }

  @Test def getBytesUTF16(): Unit = {
    val expectedBE =
      Seq(
        0, 0, 0, 9, 0, 10, 0, 65, 0, 90, 0, 97, 0, 122, 0, 48, 0, 57, 0, 64, 0,
        126, 0, -33, 78, 102, 31, 80, 0, 65
      )

    val expectedLE = expectedBE
      .sliding(2, 2)
      .toSeq
      .flatMap(_.reverse)

    val expectedWithBOM = Seq(-2, -1) ++ expectedBE

    testEncoding(StandardCharsets.UTF_16BE, expectedBE)
    testEncoding("UTF-16BE", expectedBE)
    testEncoding(StandardCharsets.UTF_16LE, expectedLE)
    testEncoding("UTF-16LE", expectedLE)
    testEncoding(StandardCharsets.UTF_16, expectedWithBOM)
    testEncoding("UTF-16", expectedWithBOM)
  }

  @Test def getBytesUnsupportedEncoding(): Unit = {
    assertThrows(classOf[java.io.UnsupportedEncodingException],
                 "This is a test".getBytes("unsupported encoding"))
  }

  @Test def literalsHaveConsistentHashCodeImplementation(): Unit = {
    assertTrue("foobar".hashCode == new String(
      Array('f', 'o', 'o', 'b', 'a', 'r')).hashCode)
  }

  @Ignore("#486")
  @Test def intern(): Unit = {
    val chars = Array('f', 'o', 'o', 'b', 'a', 'r')
    val s1    = new String(chars)
    val s2    = new String(chars)
    assertTrue(s1.intern eq s2.intern)
  }

  @Test def indexOf(): Unit = {
    assertTrue("afoobar".indexOf("a") == 0)
    assertTrue("afoobar".indexOf(97) == 0)
    assertTrue("afoobar".indexOf("a", 1) == 5)
    assertTrue("afoobar".indexOf(97, 1) == 5)
    assertTrue("".indexOf("a") == -1)
    assertTrue("".indexOf(97) == -1)
    assertTrue("".indexOf("a", 4) == -1)
    assertTrue("".indexOf(97, 4) == -1)
    assertTrue("fub??r".indexOf("a") == -1)
    assertTrue("fub??r".indexOf(97) == -1)
    assertTrue("fub??r".indexOf("a", 4) == -1)
    assertTrue("fub??r".indexOf(97, 4) == -1)
  }

  @Test def lastIndexOf(): Unit = {
    assertTrue("afoobar".lastIndexOf("a") == 5)
    assertTrue("afoobar".lastIndexOf(97) == 5)
    assertTrue("afoobar".lastIndexOf("a", 4) == 0)
    assertTrue("afoobar".lastIndexOf(97, 4) == 0)
    assertTrue("".lastIndexOf("a") == -1)
    assertTrue("".lastIndexOf(97) == -1)
    assertTrue("".lastIndexOf("a", 4) == -1)
    assertTrue("".lastIndexOf(97, 4) == -1)
    assertTrue("fub??r".lastIndexOf("a") == -1)
    assertTrue("fub??r".lastIndexOf(97) == -1)
    assertTrue("fub??r".lastIndexOf("a", 4) == -1)
    assertTrue("fub??r".lastIndexOf(97, 4) == -1)
  }

  @Test def toUpperCase(): Unit = {
    assertTrue("".toUpperCase() equals "")
    // ascii
    assertTrue("Hello".toUpperCase() equals "HELLO")
    // latin
    assertTrue("Perch??".toUpperCase() equals "PERCH??")
    // high (2 Char String) - 0x10400 or \ud801\udc00
    val iStr = new String(Character.toChars(0x10400))
    assertTrue(iStr.length equals 2)
    assertTrue(iStr.toUpperCase equals iStr)
    val bStr = "\ud801\udc00"
    assertTrue(bStr.length equals 2)
    assertTrue(bStr.toUpperCase equals "\ud801\udc00")
    assertTrue("????aaaa".toUpperCase equals "????AAAA")
    assertTrue("aaaa????".toUpperCase equals "AAAA????")
    assertTrue("aa????aa".toUpperCase equals "AA????AA")
    // partial in surrogate range
    // case of poor slicing or construction of string
    assertTrue("\ud801aaaa".toUpperCase equals "\ud801AAAA")
    assertTrue("aaaa\ud801".toUpperCase equals "AAAA\ud801")
    assertTrue("\udc00aaaa".toUpperCase equals "\udc00AAAA")
    assertTrue("aaaa\udc00".toUpperCase equals "AAAA\udc00")
    // case of one high surrogate
    val hChar = '\ud801'
    val hStr  = hChar.toString
    assertTrue(Character.isHighSurrogate(hChar))
    assertTrue(hStr.length equals 1)
    assertTrue(hStr.toUpperCase equals hStr)
    // toUpperCase should consider String's offset
    assertTrue(
      "Hi, Scala Native!"
        .subSequence(4, 16)
        .toString
        .toUpperCase equals "SCALA NATIVE")
  }

  @Test def toUpperCaseSpecialCasing(): Unit = {
    // Generated based on Unconditional mappings in [SpecialCasing.txt](https://unicode.org/Public/UNIDATA/SpecialCasing.txt)
    assertEquals("\u0053\u0053", "\u00DF".toUpperCase)       // ?? to SS
    assertEquals("\u02BC\u004E", "\u0149".toUpperCase)       // ?? to ??N
    assertEquals("\u004A\u030C", "\u01F0".toUpperCase)       // ?? to J??
    assertEquals("\u0399\u0308\u0301", "\u0390".toUpperCase) // ?? to ??????
    assertEquals("\u03A5\u0308\u0301", "\u03B0".toUpperCase) // ?? to ??????
    assertEquals("\u0535\u0552", "\u0587".toUpperCase)       // ?? to ????
    assertEquals("\u0048\u0331", "\u1E96".toUpperCase)       // ??? to H??
    assertEquals("\u0054\u0308", "\u1E97".toUpperCase)       // ??? to T??
    assertEquals("\u0057\u030A", "\u1E98".toUpperCase)       // ??? to W??
    assertEquals("\u0059\u030A", "\u1E99".toUpperCase)       // ??? to Y??
    assertEquals("\u0041\u02BE", "\u1E9A".toUpperCase)       // ??? to A??
    assertEquals("\u03A5\u0313", "\u1F50".toUpperCase)       // ??? to ????
    assertEquals("\u03A5\u0313\u0300", "\u1F52".toUpperCase) // ??? to ??????
    assertEquals("\u03A5\u0313\u0301", "\u1F54".toUpperCase) // ??? to ??????
    assertEquals("\u03A5\u0313\u0342", "\u1F56".toUpperCase) // ??? to ??????
    assertEquals("\u1F08\u0399", "\u1F80".toUpperCase)       // ??? to ?????
    assertEquals("\u1F09\u0399", "\u1F81".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0A\u0399", "\u1F82".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0B\u0399", "\u1F83".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0C\u0399", "\u1F84".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0D\u0399", "\u1F85".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0E\u0399", "\u1F86".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0F\u0399", "\u1F87".toUpperCase)       // ??? to ?????
    assertEquals("\u1F08\u0399", "\u1F88".toUpperCase)       // ??? to ?????
    assertEquals("\u1F09\u0399", "\u1F89".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0A\u0399", "\u1F8A".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0B\u0399", "\u1F8B".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0C\u0399", "\u1F8C".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0D\u0399", "\u1F8D".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0E\u0399", "\u1F8E".toUpperCase)       // ??? to ?????
    assertEquals("\u1F0F\u0399", "\u1F8F".toUpperCase)       // ??? to ?????
    assertEquals("\u1F28\u0399", "\u1F90".toUpperCase)       // ??? to ?????
    assertEquals("\u1F29\u0399", "\u1F91".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2A\u0399", "\u1F92".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2B\u0399", "\u1F93".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2C\u0399", "\u1F94".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2D\u0399", "\u1F95".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2E\u0399", "\u1F96".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2F\u0399", "\u1F97".toUpperCase)       // ??? to ?????
    assertEquals("\u1F28\u0399", "\u1F98".toUpperCase)       // ??? to ?????
    assertEquals("\u1F29\u0399", "\u1F99".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2A\u0399", "\u1F9A".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2B\u0399", "\u1F9B".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2C\u0399", "\u1F9C".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2D\u0399", "\u1F9D".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2E\u0399", "\u1F9E".toUpperCase)       // ??? to ?????
    assertEquals("\u1F2F\u0399", "\u1F9F".toUpperCase)       // ??? to ?????
    assertEquals("\u1F68\u0399", "\u1FA0".toUpperCase)       // ??? to ?????
    assertEquals("\u1F69\u0399", "\u1FA1".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6A\u0399", "\u1FA2".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6B\u0399", "\u1FA3".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6C\u0399", "\u1FA4".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6D\u0399", "\u1FA5".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6E\u0399", "\u1FA6".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6F\u0399", "\u1FA7".toUpperCase)       // ??? to ?????
    assertEquals("\u1F68\u0399", "\u1FA8".toUpperCase)       // ??? to ?????
    assertEquals("\u1F69\u0399", "\u1FA9".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6A\u0399", "\u1FAA".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6B\u0399", "\u1FAB".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6C\u0399", "\u1FAC".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6D\u0399", "\u1FAD".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6E\u0399", "\u1FAE".toUpperCase)       // ??? to ?????
    assertEquals("\u1F6F\u0399", "\u1FAF".toUpperCase)       // ??? to ?????
    assertEquals("\u1FBA\u0399", "\u1FB2".toUpperCase)       // ??? to ?????
    assertEquals("\u0391\u0399", "\u1FB3".toUpperCase)       // ??? to ????
    assertEquals("\u0386\u0399", "\u1FB4".toUpperCase)       // ??? to ????
    assertEquals("\u0391\u0342", "\u1FB6".toUpperCase)       // ??? to ????
    assertEquals("\u0391\u0342\u0399", "\u1FB7".toUpperCase) // ??? to ??????
    assertEquals("\u0391\u0399", "\u1FBC".toUpperCase)       // ??? to ????
    assertEquals("\u1FCA\u0399", "\u1FC2".toUpperCase)       // ??? to ?????
    assertEquals("\u0397\u0399", "\u1FC3".toUpperCase)       // ??? to ????
    assertEquals("\u0389\u0399", "\u1FC4".toUpperCase)       // ??? to ????
    assertEquals("\u0397\u0342", "\u1FC6".toUpperCase)       // ??? to ????
    assertEquals("\u0397\u0342\u0399", "\u1FC7".toUpperCase) // ??? to ??????
    assertEquals("\u0397\u0399", "\u1FCC".toUpperCase)       // ??? to ????
    assertEquals("\u0399\u0308\u0300", "\u1FD2".toUpperCase) // ??? to ??????
    assertEquals("\u0399\u0308\u0301", "\u1FD3".toUpperCase) // ??? to ??????
    assertEquals("\u0399\u0342", "\u1FD6".toUpperCase)       // ??? to ????
    assertEquals("\u0399\u0308\u0342", "\u1FD7".toUpperCase) // ??? to ??????
    assertEquals("\u03A5\u0308\u0300", "\u1FE2".toUpperCase) // ??? to ??????
    assertEquals("\u03A5\u0308\u0301", "\u1FE3".toUpperCase) // ??? to ??????
    assertEquals("\u03A1\u0313", "\u1FE4".toUpperCase)       // ??? to ????
    assertEquals("\u03A5\u0342", "\u1FE6".toUpperCase)       // ??? to ????
    assertEquals("\u03A5\u0308\u0342", "\u1FE7".toUpperCase) // ??? to ??????
    assertEquals("\u1FFA\u0399", "\u1FF2".toUpperCase)       // ??? to ?????
    assertEquals("\u03A9\u0399", "\u1FF3".toUpperCase)       // ??? to ????
    assertEquals("\u038F\u0399", "\u1FF4".toUpperCase)       // ??? to ????
    assertEquals("\u03A9\u0342", "\u1FF6".toUpperCase)       // ??? to ????
    assertEquals("\u03A9\u0342\u0399", "\u1FF7".toUpperCase) // ??? to ??????
    assertEquals("\u03A9\u0399", "\u1FFC".toUpperCase)       // ??? to ????
    assertEquals("\u0046\u0046", "\uFB00".toUpperCase)       // ??? to FF
    assertEquals("\u0046\u0049", "\uFB01".toUpperCase)       // ??? to FI
    assertEquals("\u0046\u004C", "\uFB02".toUpperCase)       // ??? to FL
    assertEquals("\u0046\u0046\u0049", "\uFB03".toUpperCase) // ??? to FFI
    assertEquals("\u0046\u0046\u004C", "\uFB04".toUpperCase) // ??? to FFL
    assertEquals("\u0053\u0054", "\uFB05".toUpperCase)       // ??? to ST
    assertEquals("\u0053\u0054", "\uFB06".toUpperCase)       // ??? to ST
    assertEquals("\u0544\u0546", "\uFB13".toUpperCase)       // ??? to ????
    assertEquals("\u0544\u0535", "\uFB14".toUpperCase)       // ??? to ????
    assertEquals("\u0544\u053B", "\uFB15".toUpperCase)       // ??? to ????
    assertEquals("\u054E\u0546", "\uFB16".toUpperCase)       // ??? to ????
    assertEquals("\u0544\u053D", "\uFB17".toUpperCase)       // ??? to ????
  }

  @Test def toLowerCase(): Unit = {
    assertTrue("".toLowerCase() equals "")
    assertTrue("Hello".toLowerCase() equals "hello")
    assertTrue("PERCH??".toLowerCase() equals "perch??")
    assertTrue("????AAAA".toLowerCase equals "????aaaa")
    assertTrue("AAAA????".toLowerCase equals "aaaa????")
    assertTrue("AA????AA".toLowerCase equals "aa????aa")
    // toLowerCase should consider String's offset
    assertTrue(
      "Hi, Scala Native!"
        .subSequence(4, 16)
        .toString
        .toLowerCase equals "scala native")
  }

  @Test def toLowerCaseSpecialCasing(): Unit = {
    assertEquals("\u0069\u0307", "\u0130".toLowerCase) // ?? to i??
    assertEquals("i??????i\u0307", "I????????".toLowerCase())

    /* Greek lower letter sigma exists in two forms:
     * \u03c3 '??' - is standard lower case variant
     * \u03c2 '??' - is used when it's final cased character in given word
     */
    assertEquals("??", "??".toLowerCase())
    assertEquals("????", "????".toLowerCase())
    assertEquals("d??", "D??".toLowerCase())
    assertEquals("d???? a???? b??c", "D???? A???? B??C".toLowerCase())
    assertEquals(
      "d???? a\uD804\uDC00??\uD804\uDC00??\uD804\uDC00 b??c",
      "D???? A\uD804\uDC00??\uD804\uDC00??\uD804\uDC00 B??C".toLowerCase())
    assertEquals("d????a", "D????A".toLowerCase())
    assertEquals("d????", "D????A".substring(0, 3).toLowerCase())
    // \u02B9 is not cased character
    assertEquals("d??\u02B9\u02B9??\u02B9\u02B9",
                 "D??\u02B9\u02B9??\u02B9\u02B9".toLowerCase)
    assertEquals("d??\u02B9\u02B9??\u02B9\u02B9z",
                 "D??\u02B9\u02B9??\u02B9\u02B9Z".toLowerCase)
    assertEquals("d??\u02B9\u02B9??\u02B9\u02B9",
                 "D??\u02B9\u02B9??\u02B9\u02B9Z".substring(0, 7).toLowerCase)

    /* From Unicode 13.0.0 reference, chapter 13.3, description to table 3-17.
     * The sets of case-ignorable and cased characters are not disjoint: for example, they both contain U+0345 ypogegrammeni.
     * Thus, the Before condition is not satisfied if C is preceded by only U+0345,
     * but would be satisfied by the sequence <capital-alpha, ypogegrammeni>.
     * Similarly, the After condition is satisfied if C is only followed by ypogegrammeni,
     * but would not satisfied by the sequence <ypogegrammeni, capital-alpha>.
     */
    assertEquals("\u0345??", "\u0345??".toLowerCase())
    assertEquals("\u03B1\u0345??", "\u0391\u0345??".toLowerCase())
    assertEquals("\u03B1\u0345??\u0345", "\u0391\u0345??\u0345".toLowerCase())
    assertEquals("\u03B1\u0345??\u0345\u03B1",
                 "\u0391\u0345??\u0345\u0391".toLowerCase())

  }
}
