package edu.ucla.cs.process.traditional;

import static org.junit.Assert.*;

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
	public void testMethodCallWithPrecondition() {
		String expr = "file.createNewFile()@!file.exists()";
		SequenceProcessor sp = new SequenceProcessor();
		ArrayList<String> expected = new ArrayList<String>();
		expected.add("createNewFile");
		assertEquals(expected, sp.extractItems(expr));
	}
}
