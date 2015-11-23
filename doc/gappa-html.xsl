<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <!-- import the real stylesheet -->
  <xsl:import href="http://docbook.sourceforge.net/release/xsl/current/xhtml/chunk.xsl"/>
  <xsl:import href="http://docbook.sourceforge.net/release/xsl/current/xhtml/highlight.xsl"/>

  <xsl:param name="html.stylesheet" select="'gappa.css'"/>
  <xsl:param name="navig.graphics" select="1"/>
  <xsl:param name="navig.graphics.extension" select="'.png'"/>
  <xsl:param name="header.rule" select="0"/>
  <xsl:param name="footer.rule" select="0"/>
  <xsl:param name="toc.max.depth" select="2"/>
  <xsl:param name="chunk.first.sections" select="1"/>
  <xsl:param name="variablelist.as.table" select="0"/>
  <xsl:param name="highlight.source" select="1"/>
  <xsl:param name="highlight.xslthl.config" select="'http://docbook.sourceforge.net/release/xsl/current/highlighting/xslthl-config.xml'"/>
  <xsl:param name="ignore.image.scaling" select="1"/>
  <xsl:param name="base.dir" select="'html/'"/>

<xsl:template name="header.navigation">
  <xsl:param name="prev" select="/foo"/>
  <xsl:param name="next" select="/foo"/>
  <xsl:param name="nav.context"/>

  <xsl:variable name="home" select="/*[1]"/>
  <xsl:variable name="up" select="parent::*"/>

    <div class="navheader">
        <table width="100%" summary="Navigation header">
            <tr>
              <td width="20%" align="left">
                <xsl:if test="count($prev)&gt;0">
                  <a accesskey="p">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$prev"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'prev'"/>
                    </xsl:call-template>
                  </a>
                </xsl:if>
                <xsl:if test="count($up) &gt; 0 and generate-id($up) != generate-id($home)">
                  <a accesskey="u">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$up"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'up'"/>
                    </xsl:call-template>
                  </a>
                </xsl:if>
                <xsl:if test="$home != . or $nav.context = 'toc'">
                  <a accesskey="h">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$home"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'home'"/>
                    </xsl:call-template>
                  </a>
                </xsl:if>
              </td>
              <th width="60%" align="center">
                <xsl:apply-templates select="." mode="object.title.markup"/>
              </th>
              <td width="20%" align="right">
                <xsl:if test="count($next)&gt;0">
                  <a accesskey="n">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$next"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'next'"/>
                    </xsl:call-template>
                  </a>
                </xsl:if>
              </td>
            </tr>

        </table>
    </div>
</xsl:template>


<xsl:template name="footer.navigation">
  <xsl:param name="prev" select="/foo"/>
  <xsl:param name="next" select="/foo"/>
  <xsl:param name="nav.context"/>

  <xsl:variable name="home" select="/*[1]"/>
  <xsl:variable name="up" select="parent::*"/>

    <div class="navfooter">
        <table width="100%" summary="Navigation footer">
            <tr>
              <td width="50%" align="left">
                <xsl:if test="count($prev)&gt;0">
                  <a accesskey="p">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$prev"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'prev'"/>
                    </xsl:call-template>
                  </a>
                  <xsl:apply-templates select="$prev" mode="object.title.markup"/>
                </xsl:if>
              </td>
              <td width="50%" align="right">
                <xsl:if test="count($next)&gt;0">
                  <xsl:apply-templates select="$next" mode="object.title.markup"/>
                  <a accesskey="n">
                    <xsl:attribute name="href">
                      <xsl:call-template name="href.target">
                        <xsl:with-param name="object" select="$next"/>
                      </xsl:call-template>
                    </xsl:attribute>
                    <xsl:call-template name="navig.content">
                      <xsl:with-param name="direction" select="'next'"/>
                    </xsl:call-template>
                  </a>
                </xsl:if>
              </td>
            </tr>

        </table>
    </div>
</xsl:template>

  <!-- Mathematical formulas -->
  <xsl:template name="user.head.content">
    <script type="text/x-mathjax-config">
      MathJax.Hub.Config({ config: ["MMLorHTML.js"], jax: ["input/TeX","output/HTML-CSS","output/NativeMML"] });
    </script>
    <script type="text/javascript" src="http://cdn.mathjax.org/mathjax/latest/MathJax.js"></script>
  </xsl:template>

  <xsl:template match="texinline">
    <span class="MathJax_Preview">[math]</span><script type="math/tex"><xsl:value-of select="."/></script>
  </xsl:template>

  <xsl:template match="texinformal">
    <script type="math/tex;mode=display"><xsl:value-of select="."/></script>
  </xsl:template>

</xsl:stylesheet>
