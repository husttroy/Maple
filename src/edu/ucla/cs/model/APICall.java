package edu.ucla.cs.model;

import java.util.ArrayList;

public class APICall implements APISeqItem{
	public String name;
	public String condition;
	public String receiver;
	public ArrayList<String> arguments;
	
	public APICall(String name, String condition) {
		this.name = name;
		this.condition = condition;
		this.receiver = null;
		this.arguments = null;
	}
	
	public APICall(String name, String condition, String receiver, ArrayList<String> args) {
		this.name = name;
		this.condition = condition;
		this.receiver = receiver;
		this.arguments = args;
	}
	
	@Override
	public String toString() {
		return name + "@" + condition;
	}
}
