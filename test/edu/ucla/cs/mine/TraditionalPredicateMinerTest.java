package edu.ucla.cs.mine;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashMap;

import org.junit.Test;

public class TraditionalPredicateMinerTest {
	@Test
	public void testExtractArguments() {
		String args = "getMyPath(a,c,d)+File.separator+SAVE_FILE_NAME,File.separator(d,)+SAVE_FILE_NAME,";
		// mock pattern
		ArrayList<String> pattern = new ArrayList<String>();
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		ArrayList<String> list = pm.getArguments(args);
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("getMyPath(a,c,d)+File.separator+SAVE_FILE_NAME");
		expected.add("File.separator(d,)+SAVE_FILE_NAME");
		assertEquals(expected, list);
	}
	
	@Test
	public void testExtractArguments2() {
		String args = "\"index=\"+curIndexthis+\"\\n\",";
		// mock pattern
		ArrayList<String> pattern = new ArrayList<String>();
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		ArrayList<String> list = pm.getArguments(args);
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("\"index=\"+curIndexthis+\"\\n\"");
		assertEquals(expected, list);
	}
	
	@Test
	public void testPropagatePredicateSimple() {
		String expr = "file.createNewFile()";
		String predicate = "!file.exists()";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("createNewFile");
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		HashMap<String, ArrayList<String>> map = pm.propagatePredicates(expr, predicate);
		ArrayList<String> predicates = map.get("createNewFile");
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("!rcv.exists()");
		assertEquals(expected, predicates);
	}
	
	@Test
	public void testPropagatePredicateWithChainedMethodCalls() {
		String expr = "indexEntry=new String(\"index=\"+curIndexthis+\"\\n\",).getBytes()";
		String predicate = "\"index=\"+curIndexthis+\"\\n\".length() > 0 && !new String(\"index=\"+curIndexthis+\"\\n\",).exists()";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("new String");
		pattern.add("getBytes");
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		HashMap<String, ArrayList<String>> map = pm.propagatePredicates(expr, predicate);
		ArrayList<String> predicates1 = map.get("new String");
		ArrayList<String> expected1 = new ArrayList<String>();
		expected1.add("arg0.length() > 0 && !new String(arg0,).exists()");
		assertEquals(expected1, predicates1);
		ArrayList<String> predicates2 = map.get("getBytes");
		ArrayList<String> expected2 = new ArrayList<String>();
		expected2.add("true && !rcv.exists()");
		assertEquals(expected2, predicates2);
	}
	
	@Test
	public void testPropagatePredicateWithNestedMethodCalls() {
		String expr = "saveFile=file.createNewFile(getMyPath(file,)+File.separator+SAVE_FILE_NAME,getMyPath()+File.separator+SAVE_FILE_NAME,)";
		String predicate = "!file.exists()";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("createNewFile");
		pattern.add("getMyPath");
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(pattern);
		HashMap<String, ArrayList<String>> map = pm.propagatePredicates(expr, predicate);
		ArrayList<String> predicates1 = map.get("createNewFile");
		ArrayList<String> expected1 = new ArrayList<String>();
		expected1.add("!rcv.exists()");
		assertEquals(expected1, predicates1);
		ArrayList<String> predicates2 = map.get("getMyPath");
		ArrayList<String> expected2 = new ArrayList<String>();
		expected2.add("!arg0.exists()");
		expected2.add("true");
		assertEquals(expected2, predicates2);
	}
}
