package edu.ucla.cs.model;

public class APICall implements APISeqItem{
	public String name;
	public String condition;
	
	public APICall(String name, String condition) {
		this.name = name;
		this.condition = condition;
	}
	
	@Override
	public String toString() {
		return name + "@" + condition;
	}
}
