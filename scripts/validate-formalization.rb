#!/usr/bin/env ruby
# frozen_string_literal: true
require "yaml"
require "set"
path = ARGV.fetch(0, "formalization.yaml")
meta = YAML.safe_load(File.read(path), permitted_classes: [], permitted_symbols: [], aliases: false)
abort "metadata must be a map" unless meta.is_a?(Hash)
abort "version must be v0.4" unless meta["version"] == "v0.4"
%w[project classification automation review].each { |k| abort "missing section: #{k}" unless meta[k].is_a?(Hash) }
p = meta["project"]
abort "project needs a name" unless p["name"].is_a?(String) && !p["name"].strip.empty?
abort "project needs description" unless p["description"].is_a?(String) && !p["description"].strip.empty?
abort "description too long" if p["description"].length > 10_000
abort "license must be Apache-2.0" unless p["license"] == "Apache-2.0"
%w[authors responsible_maintainers].each { |k| abort "missing #{k}" unless p[k].is_a?(Array) && !p[k].empty? }
abort "need sources" unless meta["sources"].is_a?(Array) && !meta["sources"].empty?
rels=Set["formalizes","adapts","independently-proves","background","other"]
meta["sources"].each { |s| abort "source missing title/valid relationship" unless s.is_a?(Hash) && s["title"].is_a?(String) && rels.include?(s["relationship"]) }
status=meta["status"]
abort "status missing" unless status.is_a?(Hash) && status["sorry_count"].is_a?(Integer) && status["sorry_in_definitions"].is_a?(Integer)
abort "classifications missing" unless meta["classification"].is_a?(Hash) && meta["classification"].fetch("arxiv",[]).is_a?(Array) && meta["classification"].fetch("msc2020",[]).is_a?(Array)
def scan_placeholders(x, path="root", found=[])
  case x
  when Hash then x.each { |k,v| scan_placeholders(v, "#{path}.#{k}", found) }
  when Array then x.each_with_index { |v,i| scan_placeholders(v, "#{path}[#{i}]", found) }
  when String then found << path if x.lstrip.match?(/\ATEMPLATE(?::|\z)/)
  end
  found
end
placeholders=scan_placeholders(meta)
abort "template placeholders: #{placeholders.join(', ')}" unless placeholders.empty?
puts "formalization.yaml: required fields and placeholder check passed"
