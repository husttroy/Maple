package edu.ucla.cs.model;

import java.util.HashMap;

public class Class {
	public String repo;
	public String file;
	public String clazz;
	public HashMap<String, String> fields = new HashMap<String, String>();
	
	public Class(String repo, String file, String name) {
		this.repo = repo;
		this.file = file;
		this.clazz = name;
	}
}
