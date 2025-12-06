{{- define "braidpool.fullname" -}}
{{- .Release.Name | trunc 63 | trimSuffix "-" }}
{{- end }}