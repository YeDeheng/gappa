<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:param name="latex.class.book">book</xsl:param>
  <xsl:param name="latex.class.options">twoside</xsl:param>
  <xsl:param name="ulink.show" select="1"/>
  <xsl:param name="ulink.footnotes" select="1"/>
  <xsl:param name="doc.collab.show" select="0"/>
  <xsl:param name="latex.output.revhistory" select="0"/>
  <xsl:param name="toc.section.depth" select="2"/>
  <xsl:param name="latex.bibwidelabel">99</xsl:param>
  <xsl:param name="default.table.width">autowidth.default</xsl:param>

  <!-- Mathematical formulas -->
  <xsl:template match="texinline">
    <inlineequation><alt role="tex">\(<xsl:value-of select="."/>\)</alt></inlineequation>
  </xsl:template>

  <xsl:template match="texinformal">
    <informalequation><alt role="tex">\[<xsl:value-of select="."/>\]</alt></informalequation>
  </xsl:template>

</xsl:stylesheet>
