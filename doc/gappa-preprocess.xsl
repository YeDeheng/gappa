<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output method="xml" indent="yes" encoding="UTF-8" media-type="book"
              doctype-public="-//OASIS//DTD DocBook XML V4.3//EN"
              doctype-system="http://www.oasis-open.org/docbook/xml/4.3/docbookx.dtd"/>

  <!-- Bibliography -->
  <xsl:template name="get-uri">
    <xsl:if test="@class='doi'">http://dx.doi.org/</xsl:if><xsl:apply-templates/>
  </xsl:template>

  <xsl:template match="biblioentry">
    <biblioentry>
      <xsl:choose>
        <xsl:when test="biblioset">
          <xsl:variable name="pubsnumber">
            <xsl:if test="biblioset/volumenum">
              <xsl:value-of select="biblioset/volumenum"/>
              <xsl:if test="biblioset/issuenum">
                (<xsl:value-of select="biblioset/issuenum"/>)
              </xsl:if>:
            </xsl:if>
            <xsl:value-of select="biblioset/pagenums"/>
          </xsl:variable>
          <xsl:variable name="uri">
            <xsl:for-each select="biblioset/biblioid">
              <xsl:call-template name="get-uri"/>
            </xsl:for-each>
          </xsl:variable>
          <xsl:for-each select="biblioset/*">
            <xsl:apply-templates select=".">
              <xsl:with-param name="pubsnumber" select="translate(normalize-space($pubsnumber), ' ', '')"/>
              <xsl:with-param name="uri" select="normalize-space($uri)"/>
            </xsl:apply-templates>
          </xsl:for-each>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates>
            <xsl:with-param name="uri">
              <xsl:for-each select="biblioid">
                <xsl:call-template name="get-uri"/>
              </xsl:for-each>
            </xsl:with-param>
          </xsl:apply-templates>
        </xsl:otherwise>
      </xsl:choose>
    </biblioentry>
  </xsl:template>

  <xsl:template match="biblioset/pagenums|biblioset/volumenum|biblioset/issuenum"/>
  <xsl:template match="biblioid"/>

  <xsl:template name="print-title">
    <xsl:param name="uri"/>
    <xsl:choose>
      <xsl:when test="boolean($uri)">
        <ulink>
          <xsl:attribute name="url"><xsl:value-of select="$uri"/></xsl:attribute>
          <xsl:apply-templates/>
        </ulink>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="biblioentry/title">
    <xsl:param name="uri"/>
    <title>
      <xsl:call-template name="print-title">
        <xsl:with-param name="uri" select="$uri"/>
      </xsl:call-template>
    </title>
  </xsl:template>

  <xsl:template match="biblioset/title">
    <xsl:param name="pubsnumber"/>
    <xsl:param name="uri"/>
    <xsl:choose>
      <xsl:when test="../@relation='article'">
        <subtitle>
          <xsl:call-template name="print-title">
            <xsl:with-param name="uri" select="$uri"/>
          </xsl:call-template>
        </subtitle>
      </xsl:when>
      <xsl:otherwise>
        <subtitle><emphasis><xsl:apply-templates/></emphasis></subtitle>
        <xsl:if test="boolean($pubsnumber)">
          <pubsnumber><xsl:value-of select="$pubsnumber"/></pubsnumber>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Default rule -->
  <xsl:template match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>
