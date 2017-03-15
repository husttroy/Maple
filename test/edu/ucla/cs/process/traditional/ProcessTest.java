package edu.ucla.cs.process.traditional;

import static org.junit.Assert.*;

import java.io.IOException;
import java.util.ArrayList;

import org.junit.Test;

public class ProcessTest {
	
	@Test
	public void testExtractChainedMethodCall() {
		String expr = "indexEntry=new String(\"index=\"+curIndexthis+\"\\n\",).getBytes()@";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("new String");
		expected.add("getBytes");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test
	public void testExtractNestedMethodCall() {
		String expr = "saveFile=new File(getMyPath()+File.separator+SAVE_FILE_NAME,getMyPath()+File.separator+SAVE_FILE_NAME,)@ ";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("getMyPath");
		expected.add("getMyPath");
		expected.add("new File");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test
	public void testExtractChainedMethodCallWithArgs() {
		String expr = "domainService=(DomainService) ApplicationContextHolder.getContext().getBean(\"domainService\",)";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("getContext");
		expected.add("getBean");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test
	public void testExtractCallChainAsArgs() {
		String expr = "domainService=(DomainService) ApplicationContextHolder.getContext(getBean().getArgs(a,),).getBean(\"domainService\",)";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("getBean");
		expected.add("getArgs");
		expected.add("getContext");
		expected.add("getBean");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test
	public void testMethodCallWithPrecondition() {
		String expr = "file.createNewFile()@!file.exists()";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("createNewFile");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test
	public void testExtractClassConstructorOfParameterizedType() {
		String expr = "individus=new ArrayList<>()";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("new ArrayList<>");
		assertEquals(expected, sp.extractItems(expr));
	}
	
	@Test(timeout = 5000)
	public void testSpecificLineHangsInCreateNewFile() {
		String path = "/home/troy/research/BOA/Maple/test/edu/ucla/cs/process/traditional/testHangs.txt";
		try {
			Process p = new Process();
			p.s = new SequenceProcessor();
			p.processByLine(path);
		} catch(IOException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testIsBalanced() {
		String expr1 = "adwdw)adwdw(dwkok)((()))";
		assertFalse(new SequenceProcessor().isBalanced(expr1));
		String expr2 = "adwo(aadkwo)kopadwko(())";
		assertTrue(new SequenceProcessor().isBalanced(expr2));
		String expr3 = "adwdw(\"ajiodw)jaidw\")";
		assertTrue(new SequenceProcessor().isBalanced(expr3));
		String expr4 = "adwdw(\"aji\"odw)jaidw)";
		assertFalse(new SequenceProcessor().isBalanced(expr4));
		String expr5 = "adwdw(\"aji\\\"odw)j\\\"ai\"dw)";
		assertTrue(new SequenceProcessor().isBalanced(expr5));
	}
	
	@Test
	public void testGetFirstUnbalancedCloseParenthesis() {
		String expr1 = "adwdw)adwdw(dwkok)((()))";
		assertEquals(5, new SequenceProcessor().findFirstUnbalancedCloseParenthesis(expr1));
		String expr2 = "adwo(aadkwo)kopadwko(())";
		assertEquals(-1, new SequenceProcessor().findFirstUnbalancedCloseParenthesis(expr2));
		String expr3 = "adwdw(\"ajiodw)jaidw\")";
		assertEquals(-1, new SequenceProcessor().findFirstUnbalancedCloseParenthesis(expr3));
		String expr4 = "adwdw(\"aji\"odw)jaidw)";
		assertEquals(20, new SequenceProcessor().findFirstUnbalancedCloseParenthesis(expr4));
		String expr5 = "adwdw(\"aji\\\"odw)j\\\"ai\"dw)";
		assertEquals(-1, new SequenceProcessor().findFirstUnbalancedCloseParenthesis(expr5));
	}
}
