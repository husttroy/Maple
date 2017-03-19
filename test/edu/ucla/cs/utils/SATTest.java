package edu.ucla.cs.utils;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class SATTest {
	
	@Test
	public void testStripOffUnnecessaryParentheses() {
		SAT sat = new SAT();
		String rel = sat.stripUnnecessaryParentheses("(rcv.exists())");
		assertEquals("rcv.exists()", rel);
	}
	
	@Test
	public void testSymbolizeBasic() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!rcv.exists()");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeBasicWithArg() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!rcv.exists(c)");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeDoubleNegation() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!(!rcv.exists()) && !rcv.exists()");
		assertEquals("!(!b0) && !b0", rel);
	}

	@Test
	public void testSymbolizeWithUncessaryParentheses() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!(rcv.exists())");
		assertEquals("!b0", rel);
	}

	@Test
	public void testSymbolizeWithUnbalancedParentheses() {
		SAT sat = new SAT();
		String rel = sat
				.symbolize("((s.length() + 1 > 0) || flag) && Environment.SSS");
		assertEquals("((i0 + 1 > 0) || b0) && b1", rel);
	}

	@Test
	public void testSymbolizeBug1() {
		SAT sat = new SAT();
		String p1 = "rcv.size()<firstSet.size()";
		String p2 = "true&&rcv!=null&&rcv.size()>0";
		String p1_sym = sat.symbolize(p1);
		String p2_sym = sat.symbolize(p2);
		assertEquals("i0<i1", p1_sym);
		assertEquals("true&&i2!=0&&i0>0", p2_sym);
	}
	
	/**
	 * http://stackoverflow.com/questions/12625038
	 */
	@Test
	public void testSymbolizePredicateWithParameterizedTypes() {
		SAT sat = new SAT();
		String p1 = "new ArrayList<>(rcv).size()>0";
		String p1_sym = sat.symbolize(p1);
		assertEquals("i0>0", p1_sym);
	}
	
	/**
	 * http://stackoverflow.com/questions/26032257
	 */
	@Test
	public void testSymbolizeVariableNamedAsI() {
		SAT sat = new SAT();
		String p1 = "i <= rcv.count()";
		String p1_sym = sat.symbolize(p1);
		assertEquals("i0 <= i1", p1_sym);
	}
	
	@Test
	public void testSymbolizeWithLiterals() {
		SAT sat = new SAT();
		String rel = sat.symbolize("((s.length() + 1 > 0) || (true)) && false");
		assertEquals("((i0 + 1 > 0) || true) && false", rel);
	}
	
	@Test
	public void testSymbolizeEqualsFalse() {
		SAT sat = new SAT();
		String p1 = "true && arg0!=null&&arg0.isEmpty()==false";
		String s1 = sat.symbolize(p1);
		sat = new SAT(); //clear the map
		String p2 = "rcv.exists()==false||rcv.length()<1";
		String s2 = sat.symbolize(p2);
		sat = new SAT(); // clear the map
		String p3 = "true && rcv.exists()==false && true";
		String s3 = sat.symbolize(p3);
		assertEquals("true && i0!=0&&b0==false", s1);
		assertEquals("b0==false||i0<1", s2);
		assertEquals("true && b0==false && true", s3);
	}
	
	@Test
	public void testSymbolizePlusAsStringOperator() {
		SAT sat = new SAT();
		String p = "true||StdIn.getInstance(getEncoding(),).readBooleanOption(\"Do you want to write all the configuration properties to an encrypted file at \"+rcv.getPath()+\"?\",\"y\",\"n\",)";
		String s = sat.symbolize(p);
		assertEquals("true||b0", s);
	}
	
	@Test
	public void testSymbolizeNegativeIntegers() {
		SAT sat = new SAT();
		String p = "!(from.equals(rcv,)) && true && !(rcv.getName().indexOf('.',)==-1) && !rcv.exists()";
		String s = sat.symbolize(p);
		assertEquals("!b0 && true && !(i0==-1) && !b2", s);
	}
	
	@Test
	public void testSymbolizeNull() {
		SAT sat = new SAT();
		String p = "!(entityFiles.contains(new EntityFile(rcv,null,),)) && !(rcv==null) && !(rcv.exists())";
		String s = sat.symbolize(p);
		assertEquals("!b0 && !(i0==0) && !b2", s);
	}
	
	@Test
	public void testSymbolizePlusInArgument() {
		SAT sat = new SAT();
		String p = "!rcv.substring(arg0 + arg1, arg2,).isEmpty()";
		String s = sat.symbolize(p);
		assertEquals("!b0", s);
	}
	
	@Test
	public void testSymbolizeAssignment() {
		SAT sat = new SAT();
		String p = "!(rcv = new File(propDir + f)).exists()";
		String s = sat.symbolize(p);
		assertEquals("!b0", s);
	}
	
	@Test
	public void testSymbolizeInstanceOf() {
		SAT sat = new SAT();
		String p = "!(rcv instanceof LocalFileSystem)";
		String s = sat.symbolize(p);
		assertEquals("!b0", s);
	}
	
	@Test
	public void testSymbolizeModulo() {
		SAT sat = new SAT();
		String p = "rcv % 2 > that";
		String s = sat.symbolize(p);
		assertEquals("i0 % 2 > i1", s);
	}
	
	@Test
	public void testSymbolizeStringComparison1() {
		SAT sat = new SAT();
		String p = "true && !(arg0 == null || arg0 == \"\" || arg0.isEmpty())";
		String s = sat.symbolize(p);
		assertEquals("true && !(i0 == 0 || i0 == 1 || b0)", s);
	}
	
	@Test
	public void testSymbolizeStringComparison2() {
		SAT sat = new SAT();
		String p = "true && !(arg0 == null || \"\" == arg0 || arg0.isEmpty())";
		String s = sat.symbolize(p);
		assertEquals("true && !(i0 == 0 || 1 == i0 || b0)", s);
	}
	
	@Test
	public void testZ3QueryGeneration() {
		SAT sat = new SAT();
		String p1 = "(! (== 1 a0))";
		String p2 = "(&& b0 b2)";
		String query = "(assert (or (and (not (= 1 a0)) (not (and b0 b2))) (and (not (not (= 1 a0))) (and b0 b2))))\n(check-sat)";
		assertEquals(query, sat.generateEquvalenceQueryInZ3(p1, p2));
	}
	
	@Test
	public void testZ3Runner() {
		SAT sat = new SAT();
		String query = "(declare-const a0 Int)\n(declare-const b0 Bool)\n(declare-const b2 Bool)(assert (and (not (= 1 a0)) (not (and b0 b2))))\n(check-sat)";
		assertTrue(sat.isSAT(query));
	}
	
	@Test
	public void testEqualFalse() {
		SAT sat = new SAT();
		String query = "(declare-const b0 Bool)\n(assert (= b0 false))\n(check-sat)";
		assertTrue(sat.isSAT(query));
	}
	
	@Test
	public void testEqualNegativeInteger() {
		SAT sat = new SAT();
		String query = "(declare-const i0 Int)\n(assert (= i0 -1))\n(check-sat)";
		assertTrue(sat.isSAT(query));
	}
	
	@Test
	public void testEquivalenceChecker() {
		SAT sat = new SAT();
		assertTrue(sat.checkEquivalence("true && arg0 >= 1 && !(rcv.exists())",
				"1 <= arg0 && !rcv.exists()"));
	}

	@Test
	public void testEquivalenceWithFalse() {
		SAT sat = new SAT();
		assertFalse(sat.checkEquivalence("false", "1 <= arg0 && !rcv.exists()"));
	}

	@Test
	public void testEquivalenceWithTrue() {
		SAT sat = new SAT();
		assertFalse(sat.checkEquivalence("true && arg0 >= 1 && !(rcv.exists())",
				"true"));
	}
	
	@Test
	public void testEquivalenceWithParentheses() {
		SAT sat = new SAT();
		String p1 = "!(rcv).exists()";
		String p2 = "!rcv.exists()";
		assertTrue(sat.checkEquivalence(p1, p2));
	}
	
	@Test
	public void testEquivalenceWithArguments() {
		SAT sat = new SAT();
		String p1 = "!rcv.containsKey(arg0,)";
		String p2 = "!rcv.containsKey(arg0)";
		assertTrue(sat.checkEquivalence(p1, p2));
	}
	
	@Test
	public void testImplicationChecker() {
		SAT sat = new SAT();
		assertTrue(sat.checkImplication("a&&c", "a"));
		assertFalse(sat.checkImplication("a", "a&&c"));
	}
	
	@Test
	public void testSATModuloChecker() {
		SAT sat = new SAT();
		assertTrue(sat.checkImplication("a % 2 == 1 && c", "c"));
		assertFalse(sat.checkImplication("a % 2 == 1 && c", "a"));
	}
}
