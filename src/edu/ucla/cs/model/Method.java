package edu.ucla.cs.model;

import java.util.ArrayList;
import java.util.HashMap;

import com.google.common.collect.HashMultiset;

public class Method {
	public String repo;
	public String file;
	public String clazz;
	public String method;
	public HashMap<String, String> locals = new HashMap<String, String>();
	public ArrayList<String> seq = new ArrayList<String>();
	public HashMap<String, HashMultiset<MethodCall>> calls = new HashMap<String, HashMultiset<MethodCall>>();
	public HashMap<String, HashMultiset<Assignment>> assigns = new HashMap<String, HashMultiset<Assignment>>();
	
	public Method(String repo, String file, String className, String methodName) {
		this.repo = repo;
		this.file = file;
		this.clazz = className;
		this.method = methodName;
	}
}
